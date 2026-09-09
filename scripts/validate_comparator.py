#!/usr/bin/env python3
"""Check the local proof package, without submission or authorship metadata."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
THEOREMS = ["RerandomizedSTT.problem_5_6"]
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
SHA = re.compile(r"[0-9a-f]{40}")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def validate(root: Path) -> dict:
    config_path = root / "comparator.json"
    require(config_path.stat().st_size <= 1024 * 1024, "Comparator config exceeds 1 MiB")
    config = json.loads(config_path.read_text(encoding="utf-8-sig"))
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    allowed = required | {"definition_names", "enable_nanoda"}
    require(isinstance(config, dict), "Comparator config must be an object")
    require(required <= config.keys() <= allowed, "Missing or unknown Comparator keys")
    require(config.get("enable_nanoda") is True, "NanoDa replay must remain enabled")
    require(config["theorem_names"] == THEOREMS, "The Problem 5.6 target must be retained")
    require(config.get("definition_names", []) == [], "This Challenge has no definition holes")
    axioms = config["permitted_axioms"]
    require(isinstance(axioms, list) and all(isinstance(a, str) for a in axioms), "Invalid axiom list")
    require(len(axioms) == 3 and set(axioms) == AXIOMS, "Only the three standard axioms are permitted")
    for key, expected in (("challenge_module", "Challenge"), ("solution_module", "Solution")):
        module = config[key]
        require(isinstance(module, str) and MODULE.fullmatch(module) is not None, f"Invalid {key}")
        require(module == expected, f"Expected {key}={expected}")
        require(root.joinpath(*module.split(".")).with_suffix(".lean").is_file(), f"Missing {module}.lean")
    challenge = (root / "Challenge.lean").read_text(encoding="utf-8-sig")
    require(len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000,
            "Challenge exceeds the hard review-surface limit")
    # These files use ordinary single-line imports. This is a layout check, not
    # a substitute for Lean parsing or the registry's transitive provenance audit.
    imports = re.findall(r"^\s*import\s+([^\n]+)", challenge, re.MULTILINE)
    modules = [m for line in imports for m in line.split("--")[0].split()]
    require(modules and all(m == "Mathlib" or m.startswith("Mathlib.") for m in modules),
            "The local Challenge is expected to import Mathlib modules only")
    lakefiles = [root / name for name in ("lakefile.lean", "lakefile.toml") if (root / name).exists()]
    require(len(lakefiles) == 1, "Exactly one Lakefile is required")
    require(lakefiles[0].is_file() and not lakefiles[0].is_symlink()
            and lakefiles[0].stat().st_size <= 1024 * 1024,
            "The Lakefile must be a regular file no larger than 1 MiB")
    pins = json.loads((root / "scripts/tool-pins.json").read_text())
    require(type(pins.get("minimum_landlock_abi")) is int and pins["minimum_landlock_abi"] >= 4,
            "The local runner requires Landlock ABI 4 or later")
    toolchain = (root / "lean-toolchain").read_text().strip()
    require(toolchain == pins["project_toolchain"], "Project toolchain differs from verified pins")
    require(pins["tools"]["lean4export"]["toolchain"] == toolchain, "Exporter must match project Lean")
    for name, tool in pins["tools"].items():
        require(SHA.fullmatch(tool["commit"]) is not None, f"Unpinned tool: {name}")
        require(re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\.git",
                             tool["repository"]) is not None, f"Invalid tool repository: {name}")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        require(package["type"] == "git" and SHA.fullmatch(package["rev"]) is not None,
                f"Unpinned dependency: {package['name']}")
        require(re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?",
                             package["url"]) is not None, f"Invalid dependency URL: {package['name']}")
    return {"status": "passed", "kind": "layout-config-only", "toolchain": toolchain,
            "theorem_names": config["theorem_names"], "permitted_axioms": axioms,
            "challenge_bytes": len(challenge.encode()), "challenge_lines": len(challenge.splitlines()),
            "definition_names": [], "enable_nanoda": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = validate(args.root.resolve())
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.exit(1, f"Configuration check failed: {error}\n")
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
