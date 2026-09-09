# Verification tools

`tool-pins.json` records the exact official Palomar verification tools used by
this repository. The project and `lean4export` use Lean 4.33.0; the pinned
Comparator builds with its own Lean 4.34.0-rc1 toolchain. This is the tool
selection in PalomarSubmission commit
`ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`, reviewed alongside PalomarPolicy
`e9c8c238f5695b10f75db7175648a1d0195352c1` and PalomarTemplate
`128a6c5ce5f48622e69927ccd639cbff401022e8`.

Run the following from the repository root on Linux:

```sh
python3 -m pip install --require-hashes -r scripts/verification-requirements.txt
python3 scripts/validate_comparator.py --output verification/config-check.json
python3 -m unittest discover -s scripts/tests -v
python3 scripts/validate_metadata.py
bash scripts/verify-comparator.sh
```

The complete Comparator check needs Git, Python 3 with the pinned PyYAML
parser, Elan/Lake, Go, and Rust/Cargo. It requires a non-root Linux user,
Landlock ABI 4 or newer, and a working systemd service boundary, using either
a user manager or passwordless access to the system manager. Ubuntu 24.04
GitHub-hosted runners provide the intended environment. Native Windows and
older WSL kernels fail the preflight; the script does not disable confinement
to continue. `--preflight-only` tests that boundary without building tools.

The verifier builds pinned tools, copies only Lean sources and package
configuration into a fresh directory, downloads the pinned dependency cache,
and runs the pinned Palomar active confinement controls before Comparator.
The exact comparison has `enable_nanoda: true`; a failed or skipped NanoDa
check cannot produce a successful Comparator result. No existing project
`.olean` files or Windows package junctions enter the fresh proof snapshot.
The report records source hashes, tool pins and binary hashes, the actual exit
code, and the output log. CI saves these as downloadable artifacts.

The metadata check calls the pinned registry's own structured metadata
contract. The layout validator checks the selected declaration, standard
axioms, ordinary Mathlib imports, review-surface limits, and dependency pins.
Neither is a mathematical verification. The local Comparator check does not
perform the registry's full intake, editorial review, or registration, and
does not submit anything to Palomar.

The runner and its rejection-path checks adapt the author's Graph Matrices
verification scripts to the SRHT source layout. The confinement implementation
and exporter-delimiter adapter are loaded directly from the exact pinned
PalomarSubmission checkout. The original project's `Verify.ps1` supplies the
separate full-build and transitive-axiom audit used by the Lean CI job.
