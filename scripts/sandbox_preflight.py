#!/usr/bin/env python3
"""Fail closed before downloading/building tools if Linux confinement is absent."""
from __future__ import annotations

import ctypes
import os
from pathlib import Path
import platform
import shutil
import subprocess

# Same mandatory service properties as the pinned PalomarSubmission runner.
# The complete active Landrun controls are run again by verify_comparator.py.
PROPERTIES = [
    "RestrictAddressFamilies=~AF_UNIX", "LimitNOFILE=524288", "NoNewPrivileges=yes",
    "RestrictSUIDSGID=yes", "LockPersonality=yes", "PrivateDevices=yes", "PrivateTmp=yes",
    "ProtectProc=invisible", "ProcSubset=pid", "PrivateNetwork=yes", "RuntimeMaxSec=30s",
]


def preflight(cwd: Path, minimum_abi: int = 4) -> dict:
    result = {"system": platform.system(), "release": platform.release(),
              "minimum_landlock_abi": minimum_abi, "status": "blocked", "failures": []}
    failures = result["failures"]
    if platform.system() != "Linux":
        failures.append("Comparator confinement requires Linux; native Windows is not supported")
        return result
    result["uid"] = os.getuid()
    if os.getuid() == 0:
        failures.append("Run the verifier as a non-root user")
    if platform.machine() not in {"x86_64", "aarch64"}:
        failures.append("This preflight has no reviewed Landlock syscall mapping for this architecture")
        return result
    libc = ctypes.CDLL(None, use_errno=True)
    abi = libc.syscall(444, ctypes.c_void_p(0), ctypes.c_size_t(0), ctypes.c_uint(1))
    result["landlock_abi"] = abi
    if abi < minimum_abi:
        failures.append(f"Landlock ABI {abi} is below this runner's required ABI {minimum_abi} (TCP confinement)")
    runner, true, sudo = shutil.which("systemd-run"), shutil.which("true"), shutil.which("sudo")
    result["manager_probes"] = []
    if runner is None or true is None:
        failures.append("systemd-run and true are required")
    else:
        common = ["--quiet", "--collect", "--pipe", "--wait", f"--working-directory={cwd}"]
        common.extend(f"--property={p}" for p in PROPERTIES)
        candidates = []
        if sudo:
            candidates.append(("system", [sudo, "-n", runner, *common,
                                          f"--uid={os.getuid()}", f"--gid={os.getgid()}"]))
        candidates.append(("user", [runner, "--user", *common]))
        for name, command in candidates:
            try:
                proc = subprocess.run([*command, "--", true], cwd=cwd, capture_output=True,
                                      text=True, timeout=35, check=False)
                result["manager_probes"].append({"manager": name, "exit_code": proc.returncode,
                                                 "detail": (proc.stderr or proc.stdout).strip()[:1200]})
                if proc.returncode == 0:
                    result["systemd_manager"] = name
                    break
            except (OSError, subprocess.TimeoutExpired) as error:
                result["manager_probes"].append({"manager": name, "detail": str(error)[:1200]})
        if "systemd_manager" not in result:
            failures.append("Neither a passwordless system manager nor a user systemd manager can enforce the required properties")
    if not failures:
        result["status"] = "passed"
    return result
