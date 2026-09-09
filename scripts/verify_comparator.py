#!/usr/bin/env python3
"""Pinned, confined local Comparator/NanoDa verification; never submits anything."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from sandbox_preflight import preflight
from validate_comparator import validate


def run(command: list[str], cwd: Path, env: dict | None = None) -> str:
    print("Running:", " ".join(command), flush=True)
    proc = subprocess.run(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, check=False)
    print(proc.stdout, end="", flush=True)
    if proc.returncode:
        raise RuntimeError(f"Command failed with exit {proc.returncode}: {command[0]}")
    return proc.stdout.strip()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checkout(cache: Path, name: str, pin: dict, env: dict) -> Path:
    destination = cache / name
    fresh = not destination.exists()
    if fresh:
        run(["git", "clone", "--no-checkout", "--filter=blob:none", pin["repository"], str(destination)], cache, env)
    remote = run(["git", "remote", "get-url", "origin"], destination, env)
    if remote != pin["repository"]:
        raise RuntimeError(f"Tool cache has an unexpected remote: {destination}")
    if not fresh and run(["git", "status", "--porcelain", "--untracked-files=no"], destination, env):
        raise RuntimeError(f"Refusing to overwrite modified tool sources: {destination}")
    run(["git", "fetch", "--depth", "1", "origin", pin["commit"]], destination, env)
    run(["git", "checkout", "--detach", pin["commit"]], destination, env)
    if run(["git", "rev-parse", "HEAD"], destination, env) != pin["commit"]:
        raise RuntimeError(f"Tool revision mismatch: {name}")
    return destination


def fresh_source(root: Path, work: Path) -> tuple[Path, dict]:
    """Copy sources only. Never reuse Windows packages or existing project oleans."""
    source = work / "source"
    source.mkdir()
    inputs = list(root.glob("*.lean"))
    inputs += list((root / "SRHT").rglob("*.lean"))
    inputs += list((root / "vendor").rglob("*.lean"))
    inputs += [root / name for name in ("lean-toolchain", "lake-manifest.json", "comparator.json")]
    if (root / "lakefile.toml").is_file():
        inputs.append(root / "lakefile.toml")
    hashes = {}
    for original in sorted(set(inputs)):
        if original.is_symlink() or not original.resolve().is_relative_to(root):
            raise RuntimeError(f"Source path is not a regular contained file: {original}")
        relative = original.relative_to(root)
        target = source / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, target)
        hashes[relative.as_posix()] = sha(target)
    return source, hashes


def import_verifier(registry: Path):
    path = registry / "scripts/verify_submission.py"
    name = "pinned_palomar_verifier"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load pinned confinement helpers")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def verify(args: argparse.Namespace, report: dict) -> None:
    root = args.root.resolve()
    report["stage"] = "configuration"
    report["configuration"] = validate(root)
    pins = json.loads((root / "scripts/tool-pins.json").read_text())
    report["pins"] = pins
    report["stage"] = "environment-preflight"
    report["environment"] = preflight(root, pins["minimum_landlock_abi"])
    if report["environment"]["status"] != "passed":
        report["status"] = "blocked"
        raise RuntimeError("Required confinement is unavailable; Comparator and NanoDa were not started")
    if args.preflight_only:
        report["status"] = "preflight-passed"
        return
    for command in ("git", "lake", "go", "cargo", "touch"):
        if shutil.which(command) is None:
            raise RuntimeError(f"Install the development prerequisite {command}; no automatic privileged installation is attempted")
    cache = args.cache.expanduser().resolve()
    if str(cache).startswith("/mnt/"):
        raise RuntimeError("Use a Linux-native cache directory, not a Windows-mounted build directory")
    cache.mkdir(parents=True, exist_ok=True)
    tools_dir = cache / "tools"
    tools_dir.mkdir(exist_ok=True)
    tool_env = os.environ.copy()
    # Tool builds select each repository's own pinned Lean toolchain.
    for key in ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SRC_PATH"):
        tool_env.pop(key, None)
    tool_env.update(GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_NOSYSTEM="1", GIT_TERMINAL_PROMPT="0")
    report["stage"] = "pinned-tool-builds"
    directories = {name: checkout(tools_dir, name, pin, tool_env)
                   for name, pin in pins["tools"].items() if name != "landrun"}
    for name in ("comparator", "lean4export"):
        declared = (directories[name] / "lean-toolchain").read_text().strip()
        if declared != pins["tools"][name]["toolchain"]:
            raise RuntimeError(f"Unexpected {name} toolchain: {declared}")
        run(["lake", "build", name], directories[name], tool_env)
    run(["cargo", "build", "--release", "--locked"], directories["nanoda"], tool_env)
    bin_dir = cache / "bin"
    bin_dir.mkdir(exist_ok=True)
    go_env = dict(tool_env, GOBIN=str(bin_dir), CGO_ENABLED="0")
    run(["go", "install", "github.com/zouuup/landrun/cmd/landrun@" + pins["tools"]["landrun"]["commit"]], cache, go_env)
    binaries = {
        "comparator": directories["comparator"] / ".lake/build/bin/comparator",
        "lean4export": directories["lean4export"] / ".lake/build/bin/lean4export",
        "nanoda": directories["nanoda"] / "target/release/nanoda_bin",
        "landrun": bin_dir / "landrun",
        "landrun_adapter": directories["palomar_submission"] / "scripts/landrun_passthrough.py",
    }
    if not all(path.is_file() for path in binaries.values()):
        raise RuntimeError("A pinned tool build did not produce its expected executable")
    report["binary_sha256"] = {name: sha(path) for name, path in binaries.items()}
    work = Path(tempfile.mkdtemp(prefix="verification-", dir=cache))
    source, hashes = fresh_source(root, work)
    report["work_directory"] = str(work)
    report["source_sha256"] = hashes
    report["stage"] = "trusted-dependency-cache"
    # Local Lake configuration and the SHA-pinned Mathlib dependency closure are
    # reviewed trusted inputs. This fetch builds only the dependency cache tool;
    # no Challenge/Solution/project library is built before Comparator.
    run(["lake", "exe", "cache", "get"], source, tool_env)
    for name, expected in hashes.items():
        if sha(source / name) != expected:
            raise RuntimeError(f"Dependency preparation changed source input: {name}")
    project_prefix = Path(run(["lake", "env", "lean", "--print-prefix"], source, tool_env))
    comparator_prefix = Path(run(["lake", "env", "lean", "--print-prefix"], directories["comparator"], tool_env))
    lake = project_prefix / "bin/lake"
    lean = project_prefix / "bin/lean"
    verifier = import_verifier(directories["palomar_submission"])
    verifier.supported_toolchain(pins["project_toolchain"])
    writable = source / ".lake"
    sandbox_home, sandbox_tmp = writable / "local-verifier-home", writable / "local-verifier-tmp"
    sandbox_home.mkdir(exist_ok=True)
    sandbox_tmp.mkdir(exist_ok=True)
    env = {
        "PATH": f"{project_prefix}/bin:/usr/local/bin:/usr/bin:/bin",
        "HOME": str(sandbox_home), "TMPDIR": str(sandbox_tmp), "LANG": "C.UTF-8",
        "LEAN_ABORT_ON_PANIC": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1", "GIT_TERMINAL_PROMPT": "0",
        # Comparator clears the child environment. The pinned registry adapter
        # restores fixed Git isolation settings and preserves lean4export's --.
        # It invokes real Landrun; the outer boundary below also keeps Landrun.
        "COMPARATOR_LANDRUN": str(binaries["landrun_adapter"]),
        "PALOMAR_LANDRUN_REAL": str(binaries["landrun"]),
        "COMPARATOR_LEAN4EXPORT": str(binaries["lean4export"]),
        "COMPARATOR_NANODA": str(binaries["nanoda"]),
    }
    python, touch = Path(sys.executable).resolve(), Path(shutil.which("touch")).resolve()
    executable = [project_prefix, comparator_prefix, *binaries.values(), python, touch]
    executable += [p.resolve() for p in map(Path, ("/usr", "/bin", "/lib", "/lib64")) if p.exists()]
    readable = [source, *verifier.system_readable_paths()]
    protected = [source / "comparator.json", source / "Challenge.lean",
                 directories["palomar_submission"] / "scripts/verify_submission.py"]
    snapshots = verifier.tool_snapshot([*binaries.values(), lake, lean, python, touch, *protected])
    boundary = dict(cwd=source, environment=env, landrun=binaries["landrun"],
                    writable_directories=[writable], readable_paths=readable,
                    executable_paths=executable, tools=snapshots)
    report["stage"] = "active-confinement-controls"
    # This is the actual pinned registry's composed boundary and active positive/
    # negative controls, not a permissive replacement for Landrun.
    verifier.verify_sandbox_confinement(
        work / "write-denial-probe", work / "read-denial-probe",
        positive_read=source / "Challenge.lean", python=python, touch=touch,
        protected_write_directories=[source, directories["comparator"]], **boundary)
    report["confinement_controls"] = "passed"
    report["stage"] = "comparator-and-nanoda"
    report["comparator_started"] = True
    command = [str(lake), "env", str(binaries["comparator"]), "comparator.json"]
    report["command"] = command
    proc = verifier.sandboxed_run(command, timeout=args.timeout, check=False, **boundary)
    log = work / "comparator.log"
    log.write_text(proc.stdout + "\n" + proc.stderr, encoding="utf-8")
    report["log"] = str(log)
    # Keep the complete actual run output outside the ephemeral/cache directory
    # so GitHub Actions can archive it even when Comparator or NanoDa fails.
    public_log = root / "verification/comparator.log"
    public_log.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(log, public_log)
    report["archived_log"] = "verification/comparator.log"
    report["comparator_exit_code"] = proc.returncode
    print(proc.stdout, end="", flush=True)
    print(proc.stderr, end="", file=sys.stderr, flush=True)
    for name, expected in hashes.items():
        if sha(source / name) != expected:
            raise RuntimeError(f"Verification changed source input: {name}")
    if proc.returncode != 0:
        raise RuntimeError(f"Comparator/NanoDa failed with exit code {proc.returncode}")
    report["status"] = "passed"
    report["stage"] = "complete"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--cache", type=Path, default=Path.home() / ".cache/srht-palomar")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--preflight-only", action="store_true")
    parser.add_argument("--timeout", type=int, default=19800)
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error("--timeout must be positive")
    report = {"kind": "local-comparator-verification", "status": "failed",
              "requested_mode": "preflight-only" if args.preflight_only else "full",
              "comparator_started": False, "nanoda_required": True,
              "started_at": dt.datetime.now(dt.timezone.utc).isoformat()}
    output = args.report or args.root / "verification/comparator-run.json"
    code = 0
    try:
        verify(args, report)
    except Exception as error:
        report["error"] = str(error)
        print(f"Verification did not pass: {error}", file=sys.stderr)
        code = 2 if report["status"] == "blocked" else 1
    finally:
        report["finished_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"Verification report: {output}", flush=True)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
