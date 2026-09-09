#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
exec python3 "$repository_root/scripts/verify_comparator.py" --root "$repository_root" "$@"
