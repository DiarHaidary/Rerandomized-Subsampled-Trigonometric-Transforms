# Technical report coverage

Reference: `../../ChatGPT/SRHT_Technical_Report.tex`, revised 2026-09-07 to
follow the verified operator and sampling arguments.
All names below are in the `SRHT` namespace unless explicitly qualified with
`SparseFock`. The public import `SRHT.lean`
includes every listed module. `Audit.lean` checks the principal statements and
their transitive axioms; `Verify.ps1` records the current result and source hashes.

| Report result | Lean endpoint | Coverage |
|---|---|---|
| Theorem 1, (1.6)–(1.7) | `two_round_srht_ose`, `two_round_srht_norm_failure` | Same prescribed q,D,M, actual distinct rows, limited signs, all-row endpoint. |
| Theorem 2, (1.9), full independence | `BernoulliGeneral.moment_bound` | Every real 0<ρ<1; m=ρn need not be an integer. |
| Theorem 2, limited independence | `BernoulliGeneral.moment_bound_limited` | The full inequality, with the three separate min(n,4q), min(n,4q), min(n,2q) matching assumptions. |
| Bernoulli model and expected row count | `BernoulliGeneral.gramError_eq_weightedGram`, `expected_rows` | Actual centered Gram and expectation m=ρn. |
| Five-term identity (4.4) | `SmallRows.gramKernel_normalOrder` | Exact matrix identity. |
| Small-row estimate (5.3), (5.6) | `SmallRows.effect_diagonal_norm_le`, `sign_cutoff_small_rows_norm_le` | Unconditional d+27q³ and 9(d+27q³)/n bounds. |
| Factor nine, §5.2 | `GradeCompression.grade_schur_nine` | Same positive block-Schur proof: positivity on differences, symmetric neighbor-energy counting, and polarization. |
| Lemma 3, (6.2), (6.6) | `PositiveSelector.norm_creation_le`, `norm_annihilation_le`, `norm_occupancy_le`, `norm_bernoulliOperator_le_of_sum_norm` | Noncommuting positive effects, including the sum-contraction variant. |
| Actual compressed operator, §7 | `BernoulliMoment.compressed_matrix_eq` | Exact representation and cutoff. |
| Vacuum/cutoff identity (7.3)–(7.4) | `VacuumMoment.moment_le_of_compressed_norm`, `Cutoff.matrix_cutoff_pow_of_reachability` | Compiled dependencies of the unconditional moments. |
| Limited independence, §8 | `ActualMomentTransfer.bernoulli_moment_match_min`, `fixed_sign_moment_match_min` | Exact actual-law moment equality. |
| Bernoulli tail (9.2) | `BernoulliGeneral.tail_bound`, `tail_bound_limited` | Bound d·2^(-2q), with the stronger weak norm threshold. |
| Sampling comparison and conclusion of §§10–11.1 | `ActualMomentTransfer.fixed_to_bernoulli`, `two_round_srht_norm_failure` | Finite conditional-Jensen proof; moment-root factor 4 and final constant 8192. |
| Trace-power convexity, §10.3 | `SparseFock.TracePowerConvexity.convexOn_traceEvenPower` | Same Hessian proof along symmetric affine lines, using nonnegative divided differences of odd powers; includes q=0. |
| Joint dimension/confidence order (11.5) | `rowCount_log_confidence_capped` | M≤min(n,110592001[d+log³(1/δ)]/ε²), with a universal constant. |
| Theorem 1 combined with (11.5) | `two_round_srht_ose_log_confidence` | One statement containing both the actual success probability and row bound. |
| Appendix A.1 explicit vectors | `Alignment.horizontal_norm`, `tensor_horizontal`, `tensor_vertical` | Actual unit input, H_L⊗H_L, alternating L-point supports. |
| Same normalized Walsh transform | `Alignment.tensorWalsh_eq_reindex` | Explicit bijective relabeling from H_(L²). |
| Arbitrary-round alignment | `Alignment.aligned_probability`, `evolve_of_aligned` | Exact probability 2^(-tL) and actual t-round evolution. |
| Equation (A.2) | `AlignmentObstruction.failure_lower` | Actual sampled-vector lower-tail event; no assumed alignment or failure estimate. |
| Exact miss probability | `SupportMiss.miss_probability`, `uniformRowLaw_miss_probability` | Uniform distinct-row samples on a general finite index type and the main Walsh model. |
| Equation (A.3) | `SupportMiss.missRatio_symm`, `missRatio_product`, `missRatio_lower` | Both choose-ratio identities, product formula, and power lower bound. |
| Equation (A.4) | `AlignmentObstruction.necessary_rows` | Necessary M bound from the actual failure guarantee; includes the automatic large-M branch. |
| Two-round three-quarter consequence | `AlignmentObstruction.two_round_three_quarters` | At δ=2^(-4L), M≥3/4(n-L+1). |
| Appendix A.3 asymptotic incompatibility | `GaussianObstruction.exists_dyadic_failure`, `no_universal_logarithmic_budget` | Arbitrarily large dimensions and actual failure probabilities; refutes every fixed constant C. |
| Appendix A.4 stronger event | `StrongAlignment.two_round_failure_lower` | Full disjoint 2L-by-2L signed-character family, factor 4L²2^(-2L), exact miss ratio. |

## Scope of proof correspondence

The principal conclusions in the table are formally proved. The 7 September
report revision now presents the sufficient operator norm estimates, elementary
ceiling/logarithm inequality, and finite conditional-Jensen sampling proof used
in Lean. Equation (4.25) includes the norm-bound correction cost, (11.4) is the
explicit cubic-log bound, and Section 10 derives the finite moment comparison.
The follow-up revision also aligns the two residual proof methods: Section 5.2
uses the positive block-Schur argument and Section 10.3 uses the trace-power
Hessian argument. These replace valid alternative proofs of the same bounds.
The preceding report used a sharper leverage-sensitive intermediate estimate
and a continuous-priority/Chernoff sampling argument; those earlier exports
are preserved under ChatGPT/report_build/pre_lean_revision_2026_09_07/.
The explanatory report is still mathematical prose rather than a literal
line-by-line presentation of proof-assistant syntax.

Appendix A's ambient parameters are L=2^k and n=L². Some formal endpoints
also permit k=0, t=0, or M=0; this extends their valid range and includes the
report's k≥1, t≥1, 1≤M≤n conditions. The necessary-row endpoints assume a
failure upper bound because that is exactly the premise of a necessary
condition. The probability lower bounds and the final impossibility theorem
do not assume the obstruction they establish.

The bibliography, claimed research novelty, code-experiment counts, and
source-provenance statements in Sections 12 and Appendix B are not mathematical
theorems in Lean. Formal verification here applies to the specified finite
Walsh model and quantitative conclusions, not to those historical assertions.
