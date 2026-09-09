#!/usr/bin/env python3
"""Apply the pinned Palomar metadata contract without contacting its service."""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import subprocess
import sys

from verify_comparator import checkout, import_verifier, sha


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--policy-directory", type=Path)
    parser.add_argument("--cache", type=Path, default=Path.home() / ".cache/srht-palomar")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output or root / "verification/metadata-check.json"
    report = {"kind": "pinned-palomar-metadata-contract", "status": "failed",
              "checked_at": dt.datetime.now(dt.timezone.utc).isoformat()}
    code = 0
    try:
        pin = json.loads((root / "scripts/tool-pins.json").read_text())["tools"]["palomar_submission"]
        report["policy_commit"] = pin["commit"]
        if args.policy_directory:
            policy = args.policy_directory.resolve()
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=policy,
                                               text=True).strip()
            if revision != pin["commit"]:
                raise ValueError("The supplied policy checkout does not match tool-pins.json")
        else:
            cache = args.cache.expanduser().resolve() / "tools"
            cache.mkdir(parents=True, exist_ok=True)
            env = dict(os.environ, GIT_TERMINAL_PROMPT="0", GIT_CONFIG_GLOBAL="/dev/null",
                       GIT_CONFIG_NOSYSTEM="1")
            policy = checkout(cache, "palomar_submission", pin, env)
        verifier = import_verifier(policy)
        metadata = verifier.submission_contract.load_formalization_metadata(root / "formalization.yaml")
        report.update(status="passed", metadata_sha256=sha(root / "formalization.yaml"),
                      project_name=metadata["project"]["name"],
                      declared_license=metadata["project"]["license"],
                      scope="Structured metadata minimum; no editorial review, license detection, or registry submission")
    except Exception as error:
        report["error"] = str(error)
        print(f"Metadata check failed: {error}", file=sys.stderr)
        code = 1
    finally:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(report, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
