# Independent model and endpoint audit

Date: 2026-09-07. Reviewer: `srht_literature` agent.

**Initial audit status:** Model, normalization, distributional transfer, finite constants, and the final unconditional statements in `SRHT/Main.lean` **pass this source-level audit**. The subsequent kernel result is recorded below. This is a statement/model audit, not a fresh audit of every line of the long operator proof.

## Concrete mathematical model

The following definitions match the intended two-round Walsh SRHT exactly.

- `WalshIndex k = Fin k → ZMod 2` has cardinality `n = 2^k`; `walshMatrix` is the normalized real Walsh character matrix, with entries `n^(-1/2) χ(a,b)` and proved orthogonality.
- `Model.twoRoundMatrix x y` is `H * D_y * H * D_x`, where `bitSign 0 = 1` and `bitSign 1 = -1`. The order of the two sign families agrees with the intended first and second diagonals.
- For a fixed real frame `U` with `U.transpose * U = 1`, `transformedFrame U x y` is `H D_y H D_x U`.
- `sampledFrame U x y T` has rows indexed by the actual elements of the finite set `T` and entries `sqrt(n / T.card) * transformedFrame U x y j b`. Its proved Gram identity gives precisely `(n / |T|) Σ_{j∈T} w_j w_jᵀ`.
- `RowSet k M` is the subtype of finite sets with cardinality exactly `M`. `uniformRowLaw` assigns every such set equal mass. Thus this is uniform sampling of distinct rows; no iid row labels or multiplicities are substituted. Using unordered subsets instead of an ordered row list does not change the norm or Gram conclusion.

The only frame hypothesis is `UᵀU = I`. There is no coordinate-support, incoherence, lower bound on the ambient-to-subspace ratio, or supplied operator estimate in the concrete model. The implied inequality `d ≤ n` need not be an additional premise: it follows from the existence of such an isometric frame.

## Actual probability laws and limited independence

`FiniteLaw` consists of nonnegative weights summing to one; `expect` and `prob` are their literal finite sums. The full sign law is the product of independent uniform bits. The final sampling law is nested as

`μx.product (μy.product (uniformRowLaw hM))`.

This imposes independence between the two sign families and the row sample, while permitting limited independence within each sign family.

`MatchesUpTo μ (signLaw k) K` quantifies over **all** observables depending on at most `K` named coordinates. It therefore asserts genuine matching coordinate marginals, rather than assuming the desired matrix moment. The required order `min(n, 4q)` agrees with the trace-moment degree: each frame entry has degree one in each sign family, each Gram entry has degree two, and the even trace power has degree at most `4q` in each family. `fixed_sign_moment_match_min` transfers the actual fixed-row trace moment under this assumption.

The occupation basis weights are proved to equal these actual product laws (`TwoSignRepresentation.basis_law`, `OccupationBasis.signs_law`, and `OccupationBasis.bernoulli_law`). No uniform weighting of nonuniform Bernoulli outcomes is used.

## Gram, error, and vector conclusion

`TwoSignRepresentation.rowEffect U j` is literally `w_j w_jᵀ`, and its sum is the identity under `UᵀU = I`. Its finite-basis representation is an actual multiplication matrix, not a substitute operator assumed to share moments.

At `p = M/n`, `BernoulliRepresentation.error` is

`Σ_j (η_j/p - 1) w_j w_jᵀ`.

Consequently it is the correctly centered Bernoulli Gram error. `ActualMomentTransfer.centeredSum_sampledGram`, `supportMoment_eq`, and `bernoulli_error_weightedGram` preserve this normalization exactly.

`FixedSizeTail.IsOSE` requires both inequalities simultaneously for **every** vector `v` in the Euclidean space `R^d`:

`(1-ε) ||v||² ≤ ||sampledFrame v||² ≤ (1+ε) ||v||²`.

`gram_norm_iff_ose` identifies this with the genuine Euclidean operator norm condition `||sampledGram - I|| ≤ ε`. The norm scope is `Matrix.Norms.L2Operator`, and the sampled frame action is `applyRectMatrix` on `EuclideanSpace`; the endpoint is not an entrywise or coordinatewise norm bound. The tail helper uses `ε ≤ ||error||`, a stronger bad event than the strict failure event needed for the non-strict OSE inequalities.

Full sampling is handled separately: `M = n` forces `T = univ`, `sampledGram_full` proves exact identity for every sign assignment, and `full_rows_success` proves success probability one. No division at `p = 1` or positive-variance Bernoulli basis is needed in that branch.

## Parameters and verified changes in proof route

The parameter definitions agree with the finite target:

`q = ceil(log(4d/δ) / (2 log 2))`,

`D = d + 27 q³`,

`M = min(n, ceil(8192 D / ε²))`.

The statistical helpers allow `d ≥ 1`, `0 < ε ≤ 1`, and `0 < δ < 1/2`, with arbitrary natural `k`. The final `Main` endpoint uses exactly the intended strict range `0 < ε < 1` and explicitly includes `1 ≤ d ≤ n`. Proper sampling has proved `M > 0` and `M < n`. The parameter lemmas establish `d * 2^(-2q) ≤ δ/4` and `4 * (6 sqrt(D/M) + 9D/M) ≤ ε/2` under the prescribed proper-sampling row count.

Two formal proof choices differ from the earliest handwritten route but do not weaken the endpoint:

1. **Negative correction.** `SmallRowsNormalBound.gramKernel_compressed_norm_le` bounds the negative normal-order term in absolute norm, paying an additional `2p` instead of dropping it by positivity. The resulting collected bound is `d + 3p + p s + |T| s`. The compiled `small_row_cost_le` includes this extra cost and still proves the final allowance `d + 27q³`. `SmallRowsFinal.effect_diagonal_norm_le` and `sign_cutoff_small_rows_norm_le` have only the concrete isometry, grade, and cardinality premises; they do not assume the small-row estimate.
2. **Fixed-size sampling.** The formal argument uses the exact finite fill/thin coupling and convex even-trace-power Jensen inequality at `p=M/n`, not continuous priorities and a Chernoff exceptional event. `Sampling.bernoulli_trace_moment_transfer` gives a factor `4^(2q)` through the proved retention lower bound `1/4`. Thus the fixed-size moment envelope is four times the Bernoulli envelope. The existing constant `8192` absorbs that factor directly. There is no unaccounted binomial tail or iid row replacement.

## Final endpoint binder review

The statistical helper `FixedSizeTail.rowCount_success_of_bernoulli_bound` explicitly takes the actual Bernoulli moment bound as an intermediate premise. This helper is not presented as the final unconditional theorem.

The source statement `BernoulliMoment.moment_bound` is the exact unconditional estimate needed to discharge that premise: its only mathematical inputs are the concrete isometric frame, positive moment order, and `0 < M < n`; all occupation, reachability, positivity, and deterministic small-row bounds are used internally.

The final saved `SRHT/Main.lean` has now been read directly. Its three endpoints are:

- `SRHT.two_round_srht_ose`: success probability at least `1-δ` for the actual simultaneous Euclidean OSE event, under the separate limited-independence assumptions above.
- `SRHT.two_round_srht_norm_failure`: probability at most `δ` of `ε ≤ ||sampledGram-I||` under the same distribution and parameters.
- `SRHT.two_round_srht_ose_independent`: the fully independent-sign specialization under the literal `sketchLaw`.

The final binders are an arbitrary natural `k`, an arbitrary real `2^k × d` frame `U`, `UᵀU = I`, `1 ≤ d ≤ 2^k`, `0 < ε < 1`, `0 < δ < 1/2`, and, for the limited-sign versions, the two stated marginal-matching laws. The explicit `d ≤ n` premise is standard and redundant for an isometric frame; it is not an ambient-growth restriction. The exact prescribed `rowCount` is used inside `uniformRowLaw` in the conclusions.

Both general endpoints invoke `BernoulliMoment.moment_bound` internally to discharge the intermediate Bernoulli estimate. There is **no remaining `hBern`, `hsub`, assumed moment estimate, incoherence bound, supplied embedding property, or dimension-growth hypothesis in any final theorem binder**. The independent specialization discharges the two matching assumptions by reflexivity against `signLaw`.

The distribution used in the conclusion is independent of the tested frame `U`. Thus the statement is an oblivious embedding guarantee for every fixed subspace represented by an orthonormal frame, not a distribution adapted to that frame. The formal finite statement matches the Session 5 target and gives the intended constant-confidence optimal-row consequence; the source-level review makes no separate claim about novelty.

**Result:** no model, normalization, quantifier, or hidden-hypothesis mismatch found.

**Subsequent kernel verification:** the root agent ran `Verify.ps1` successfully on 2026-09-07 at 15:32:07 UTC. All 3348 build jobs passed; all nine transitive-axiom inventories contained only `propext`, `Classical.choice`, and `Quot.sound`; the source scan found no unfinished proofs or custom axioms. The final public OSE and norm-failure theorems are included in this audit. Logs and the SHA-256 manifest of 109 source/configuration files are in `verification/`.

## Expanded report audit following Claude's criticism

Date: 2026-09-07. Independent statement/model reviewer: `srht_literature`.
This section supersedes the earlier scope assessment; the current verification
files supersede the historical nine-result run described above.

**Source-audit result: PASS for the principal report statements and Appendix A.**

- `BernoulliGeneral` permits every real 0<ρ<1 and real m=ρn. It uses the
  actual centered Gram, independent or limited-independent product laws, and
  the required separate 4q/4q/2q coordinate-matching orders. Its finite tail
  has the report's 256D/a² size premise. The deterministic ρ=1 endpoint
  correctly has zero error when every selector is one.
- `LogConfidence` and `Quantitative` prove the actual OSE together with a
  universal cubic-logarithmic confidence bound and the ambient n cap. No
  δ-dependent coefficient is presented as a universal constant.
- `Alignment` constructs the report's unit horizontal vector, actual HD_j
  steps, fully independent signs, and alternating supports. `TensorWalsh`
  explicitly identifies H_L⊗H_L with the ordinary normalized Walsh matrix
  on 2k binary coordinates after a bijective relabeling.
- `SupportMiss` and `AlignmentObstruction` connect exact combinatorial
  probabilities to the actual sampled-vector lower tail. The necessary row
  count covers the automatic near-full case and gives the two-round 3/4
  consequence.
- `GaussianObstruction` is a probabilistic impossibility statement, not only
  scalar growth. For each fixed round count and distortion, every proposed
  constant C fails at arbitrarily large dyadic dimensions and valid confidence
  levels. The statement even allows M to be chosen separately for each
  dimension/confidence pair. A single unit-vector family, hence d=1, suffices.
- `StrongAlignment` uses all 2L distinct signed characters per stage. The
  first support is vertical and the final support horizontal; distinct pairs
  define disjoint events. The actual independent two-sign/uniform-row law
  gives factor (2L·2^(-L))² times the exact miss ratio.

No hidden analytic assumptions, incorrect bias, norm, normalization, support
swap, or model weakening were found. The prior main theorem was correct;
the earlier description of the entire report as complete was too broad. The
principal-statement omissions identified by Claude are now supplied. Valid
alternative intermediate operator estimates and the finite Jensen sampling
proof remain in use, so this is not a line-by-line transcription of the report.

This independent audit inspected statements and models. The full build,
expanded transitive-axiom inventory, and source scan are recorded separately
by `Verify.ps1` in `verification/result.json` and its accompanying logs.
