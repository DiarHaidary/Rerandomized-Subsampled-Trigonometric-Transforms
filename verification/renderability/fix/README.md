# Applied Challenge rendering compatibility fix

Challenge and Solution now give the existing finite enumeration of `Index k`
the name `indexFintype`. The instance is defined by `inferInstance`; it does not
replace the enumeration, change the transform, or weaken the theorem.
The selected theorem's documentation also explicitly identifies real Walsh
space of order `2^k`, making its scope visible in Palomar's isolated display.

## Confirmed server failure on the previous commit

Palomar's [render run 34393234056](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34393234056)
failed for commit `76867341d4fe08702921aa12b88624ebb7831b4f` with the same
`ZMod.fintype 2` / `NeZero` mismatch reproduced in the original local audit.
The actual artifact report and retrieval provenance are preserved as
`server-failure-report.json` and `server-failure-provenance.json`.
Palomar classified this deterministic audit error as retryable, explaining
the repeated rendering attempts shown on the submission page.

The audit creates a separate printing environment with opaque stand-ins for
non-core definitions. Expanding the inferred enumeration into the theorem's
type crosses a definitional equality that these stand-ins erase. Naming the
existing enumeration prevents that expansion. This is a compatibility change
to the Challenge interface, not a change to the underlying mathematical proof.

## Fresh checks

- Complete local Lean build: passed, including the modified Solution, 3,362 jobs.
- All 33 transitive axiom audits and the proof-source scan: passed. The only
  permitted foundations remain `propext`, `Classical.choice`, and `Quot.sound`.
- Challenge/configuration layout: passed, 89 lines and 4,484 bytes.
- Verso literate build with the official trusted renderer configuration: passed.
- **Unmodified official core-notation audit on the changed Challenge: passed.**
  Its actual output is `core-notation-audit.json`; stderr is empty.

`local-checks.json` records the source hashes and exact tool revisions.
The build and axiom evidence is retained in `../../build.log`,
`../../axioms.log`, and `../../result.json`. These checks ran locally on
Windows. The Verso checkout was restored to its pinned, unmodified source
before the final literate build. No audit output was fabricated, and no
renderer or audit patch is part of this fix.

Fresh Linux Comparator and NanoDa verification is required for this changed
snapshot; its result will be linked here after CI finishes. This local record
does not claim a complete Palomar server rendering pass, automated review,
or registration. The earlier successful CI result remains attached to its
original checked source commit.

## Existing Palomar submission

The submission shown by the user is pinned to commit `7686734` and that
commit's Challenge hash. A GitHub push cannot replace its source. A new
submission must select the corrected full commit SHA and `comparator.json`.
No submission was created, withdrawn, or registered by this change.
