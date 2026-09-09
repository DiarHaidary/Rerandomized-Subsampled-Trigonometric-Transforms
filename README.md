# Rerandomized Subsampled Trigonometric Transforms

**Verified compatibility fix:** the complete Linux build, all 33 axiom
audits, Comparator, NanoDa, and Lean's default kernel passed for source commit
`261302eb6c6d2c37f726e92801ff7f790e8dcbc1`. The
[new verification record](verification/ci/34396410088/README.md) preserves the
reports and exact checked commit. The
[historical record](verification/ci/34373116757/README.md) for the earlier
source commit `f813b5c3c14ddda0cd0dc429e657b0dbe6f94079` remains available.

**Rendering compatibility update:** Challenge and Solution now name their
existing finite-index instance `indexFintype`. This addresses the `ZMod 2`
dependency failure documented in the
[original renderability report](verification/renderability/README.md).
Fresh local checks pass: the complete Lean build, all 33 axiom audits, the
proof-source scan, the trusted Verso literate build, and the unmodified
official core-notation audit. Their evidence is recorded
[separately](verification/renderability/fix/); the new Linux CI record above
confirms Comparator and NanoDa for the changed sources. These checks do not
establish a complete Palomar server rendering pass or acceptance.

This repository contains the complete Lean proof development for two-round
Walsh SRHT embedding bounds and a Palomar Challenge/Solution interface for
[Problem 5.6 of *Linear Systems and Eigenvalue Problems: Open Questions from a
Simons Workshop*, arXiv:2602.05394v3](https://arxiv.org/pdf/2602.05394v3#page=42).

The compared theorem is **`RerandomizedSTT.problem_5_6`**. It states the
embedding probability and the dimension-linear sample bound together.
[Challenge.lean](Challenge.lean) defines the actual transform and uniform
sampling using Mathlib alone. [Solution.lean](Solution.lean) proves the same
statement from the included development. The Challenge's single intentional
proof hole is the statement Comparator is asked to verify; the Solution and
proof library contain no unfinished proofs or additional mathematical axioms.

## The result

Let `n = 2^k`, `1 <= d <= n`, and let `U` be any real `n`-by-`d` matrix with
orthonormal columns. For `0 < epsilon < 1` and `0 < delta < 1/2`, define

```text
q = ceil(log_4(4d/delta))
M = min(n, ceil(8192 (d + 27q^3) / epsilon^2)).
```

Draw two independent uniform sign vectors `x,y` and, independently, a uniform
`M`-element set of distinct rows. With `H` the normalized Walsh matrix, set

```text
A = sqrt(n/M) R H D_y H D_x.
```

With probability at least `1-delta`, simultaneously for every vector `v`,

```text
(1-epsilon) ||v||_2^2 <= ||A U v||_2^2 <= (1+epsilon) ||v||_2^2.
```

The same compared theorem proves `1 <= M <= n` and

```text
M <= (8192 (1 + 432/delta) + 1) d / epsilon^2.
```

For any fixed failure probability, this is the `O(d/epsilon^2)` row bound
asked for in Problem 5.6, with a constant independent of `n,d,epsilon`.
Every fixed real subspace can be represented by an orthonormal frame `U`;
the random matrix's distribution does not depend on that frame. The source's
column sketch `Omega = sqrt(n/M) D_x H D_y H R^T` is the transpose of `A`.

The statement covers dyadic Walsh dimensions, including `n=1`, and exact
sampling of all rows when the row budget saturates. It does not impose an
additional logarithmic ambient-size condition. It does not assert the same
result for arbitrary Fourier, cosine, or other trigonometric transforms.
Its constant depends on the fixed failure probability; no uniform Gaussian
confidence bound is claimed. See the detailed
[source correspondence](notes/SOURCE_FIDELITY.md).

## Repository layout

| File or directory | Purpose |
|---|---|
| [Challenge.lean](Challenge.lean) | Small, independently compiled mathematical statement; imports only Mathlib |
| [Solution.lean](Solution.lean) | Complete proof of the identical statement and explicit definitions |
| [comparator.json](comparator.json) | Selected theorem, allowed foundations, required NanoDa replay |
| [formalization.yaml](formalization.yaml) | Source, scope, authorship, automation, license, and review metadata |
| [SRHT/](SRHT/) | Full SRHT proof development |
| [vendor/sparse-fock/](vendor/sparse-fock/) | Included reusable finite probability and operator proof sources |
| [Audit.lean](Audit.lean) | Transitive axiom audit of the compared theorem and 32 underlying results |
| [docs/SRHT_Technical_Report.pdf](docs/SRHT_Technical_Report.pdf) | Informal proof account, also supplied as Markdown and LaTeX |
| [scripts/](scripts/) | Layout checks and pinned, confined Comparator/NanoDa runner |
| [verification/](verification/) | Actual verification records; each record identifies the checks it ran |

The larger proof library also proves limited-independence variants, a
Bernoulli moment theorem, a cubic-logarithmic confidence bound, and
support-alignment obstructions. These results are retained and audited by
Lean but are not additional selected claims in `comparator.json`.
[REPORT_COVERAGE.md](notes/REPORT_COVERAGE.md) maps the technical report to
those declarations.

## Build and verification

Lean **4.33.0** is fixed in `lean-toolchain`. Mathlib and its transitive
dependencies are pinned to exact Git commits in `lake-manifest.json`.
No local path dependency or precompiled proof is needed by a fresh checkout.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

On Windows, `./Verify.ps1` also scans proof sources and writes a timestamped
source-hash inventory. Its result concerns Lean and the axiom audit.
The only allowed foundations are `propext`, `Classical.choice`, and `Quot.sound`.

The Linux verification workflow additionally runs Comparator and NanoDa
inside Landrun confinement, using the revisions recorded in
[scripts/tool-pins.json](scripts/tool-pins.json). It compares the theorem's
statement and the definitions on which it depends, then checks the exported
proof with NanoDa. Its report is separate from the ordinary Lean build.
See [Palomar criteria and check status](notes/PALOMAR_CRITERIA.md) for the
exact distinction between repository checks and registry review.

The submitter's Palomar status page records a submission of commit
`76867341d4fe08702921aa12b88624ebb7831b4f` on 9 September 2026 at 17:48:26 UTC,
mechanical verification success at 18:00:19 UTC, and a Challenge-rendering
retry at 19:14:51 UTC. Automated review completion and registration are not
established by that status. The submission selects that exact old commit;
pushing the compatibility update does not change its selected snapshot.
The fixed sources require a submission selecting their new public commit.

## Sources, provenance, and process

The requested source is **Problem 5.6**, with the transform defined in
Definition 5.3 and the embedding convention in Definition 5.1 of the cited
workshop paper. The informal proof source is this project's
[7 September 2026 technical report](docs/SRHT_Technical_Report.md).
The paper poses the question; it is not the source of the proof developed here.
Publication priority and novelty have not been independently established.

The proof proceeds through finite multiplication operators, a small-set row
estimate, a positive selector moment estimate, a finite conditional-Jensen
comparison to exact-size row sampling, and the matrix tail bound. The final
statement assumes no moment or operator estimate. Its proof imports those
results only after proving them in the included sources.

Diar Heidary directed the project. The research development, Lean proofs,
packaging, and audits were produced with substantial AI-agent assistance
through Codex; the available review is machine checking and AI-assisted
statement inspection, not independent human mathematical review. Metadata
records the process and limitations explicitly.

The [MIT License](LICENSE) follows the existing license of the author's
related formalization. Reused SparseFock code retains its
[MIT notice](vendor/sparse-fock/LICENSE); dependency licenses and the cited
paper's rights remain their own. [Provenance](docs/PROVENANCE.md) records
source hashes and the upstream revision.
