# Linux verification of the rendering compatibility fix

[GitHub Actions run 34396410088](https://github.com/DiarHaidary/Rerandomized-Subsampled-Trigonometric-Transforms/actions/runs/34396410088)
completed successfully on 9 September 2026. Both the Lean verification job
and the Comparator job passed for source commit
`261302eb6c6d2c37f726e92801ff7f790e8dcbc1`.

- The complete Linux Lean build and all 33 transitive axiom audits passed.
  The audited declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`. The proof-source scan also passed.
- Comparator accepted `RerandomizedSTT.problem_5_6` from Solution against
  Challenge. NanoDa and Lean's default kernel both accepted the exported
  solution. The required Linux confinement checks passed.
- All 121 source hashes in the downloaded Comparator report were compared
  with the exact Git blob bytes at the checked commit; every hash matched.
  `source-hash-check.json` records that additional check.

`lean/` and `comparator/` preserve the downloaded reports and logs without
editing their contents. `workflow-run.json` records the run status and
checked commit. Exact tool revisions are in `comparator/comparator-run.json`.

The Challenge hash for this snapshot is
`2014066db73506991b7fb4402c27ec0b92cf94f9dd28906c9157a01f0df2a690`.
The named finite-index instance fixes the previously reproduced rendering
audit failure; the separate [local rendering record](../../renderability/fix/)
contains the successful unmodified official audit and Verso literate build.

This CI record establishes proof verification and comparison for the exact
source snapshot. It does not establish a complete Palomar server rendering
pass, automated review, or registration. The previous Palomar submission
remains pinned to its old commit; a new submission must select a corrected
snapshot with `comparator.json`.
