# Verified Linux snapshot

GitHub Actions run:
https://github.com/DiarHaidary/Rerandomized-Subsampled-Trigonometric-Transforms/actions/runs/34373116757

Checked source commit:
`f813b5c3c14ddda0cd0dc429e657b0dbe6f94079`

Both jobs passed on 9 September 2026:

- The complete Lean build, all 33 transitive axiom audits, proof-source scan,
  layout checks, and pinned Palomar metadata-contract check passed.
- Comparator matched `RerandomizedSTT.problem_5_6` and its definitions between
  Challenge and Solution. NanoDa and Lean's default kernel both accepted the
  exported solution. The required active confinement controls passed.

The downloaded job artifacts are retained verbatim in `lean/` and `comparator/`.
The Comparator report includes exact tool pins, binary hashes, and hashes of
all 121 fresh source inputs. The workflow run record identifies the exact
public commit. The status here records repository CI, not a Palomar server
submission, editorial review, or registry registration.

This evidence was added in a later documentation-only commit. No mathematical
source, build configuration, metadata, or verifier was changed by that commit.
Use the full checked commit above when a verified snapshot identifier is needed.
