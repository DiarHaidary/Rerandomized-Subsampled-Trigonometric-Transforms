# Assessment of Claude's audit

Date: 2026-09-07. Reference: the user-supplied audit of
`ChatGPT/SRHT_Technical_Report.tex` against the earlier Lean project.

**Subsequent report revision:** at the user's request, the technical report
was revised on 2026-09-07 to present the verified norm-bound operator estimates
and finite Jensen sampling proof. It also uses the explicit Lean log-confidence
calculation. The discussion below records the audit against the preceding
report; the old exports are retained in the report build's dated backup folder.

**Follow-up method audit:** the remaining observations about Sections 5.2 and
10.3 were also valid. The report has now replaced its generic sparse-block
norm estimate with Lean's positive block-Schur proof, and its eigenvector-mixing
Jensen proof with Lean's nonnegative-Hessian proof of trace-power convexity.
The statements, constants, and Lean source are unchanged. The preceding report
exports are preserved in `ChatGPT/report_build/pre_method_alignment_2026_09_07/`.

## Verdict

The coverage criticisms are valid. They identify omissions and weaker
corollaries, not a counterexample or an invalid proof of Theorem 1.
The earlier complete-build and nine-axiom-audit report was accurate for the
then-existing project, but it did not establish complete coverage of the
consolidated report. Describing that as complete report verification was too
broad. A successful compiler run verifies the actual statements it receives;
it does not establish that all statements in a separate document were included.

## Warranted changes

1. **General Bernoulli rate.** The earlier unconditional moment theorem only
   used ρ=M/n for a natural M. `BernoulliGeneral.moment_bound` now proves the
   inequality for every real 0<ρ<1. The actual expected selector count is proved
   to equal m=ρn. No integrality or supplied small-subset estimate is assumed.

2. **Limited-independence composition.** The earlier moment equality was
   valid but separate. `BernoulliGeneral.moment_bound_limited` now composes it
   with the unconditional arbitrary-rate estimate, with exactly the report's
   min(n,4q), min(n,4q), min(n,2q) marginal-matching orders. The associated
   limited-independent Bernoulli tail is also a named theorem.

3. **Logarithmic confidence dependence.** The former bound with a coefficient
   proportional to 1/δ only proved the fixed-confidence consequence. It did
   not prove (11.5). The new bound is

       M ≤ min(n, 110592001 [d+log³(1/δ)] / ε²).

   Its universal constant is intentionally conservative. The proof uses
   q³ ≤ 16d+500log³(1/δ), then the original rowCount definition. `Quantitative`
   combines the bound with the actual embedding theorem.

4. **Appendix A.** The previous project had no counterpart. The new modules
   prove its explicit alternating Walsh supports, unit normalization,
   independent sign alignment probabilities, exact row-miss probability,
   necessary row count, two-round 3/4 corollary, arbitrarily large-dimensional
   confidence obstruction, and stronger two-round signed-character family.
   The final statements concern actual sampled-vector failure probabilities;
   they do not leave the support alignment or failure lower bound as premises.

## Valid differences that were retained

- The finite fill/thin coupling and conditional Jensen argument replace the
  report's continuous-priority and Chernoff route. The proved factor 4 in the
  moment root is already absorbed by the original 8192 constant.
- Bounding the negative normal-order correction in absolute norm adds an
  intermediate term but still gives the required d+27q³ bound. This does not
  reproduce the sharper leverage-sensitive intermediate equation (4.25).
- Using the bound μ≤1 is sufficient for the main small-row estimate.
- The weak norm threshold ≥ε proves a stronger probability bound than >ε.
  The explicit d≤n premise is redundant for an isometric frame; unordered
  subsets preserve the exact sampled Gram. The full-row endpoint is covered.

Thus this project verifies the report's principal conclusions with documented
alternative proofs. It does not claim to have separately proved every
intermediate displayed estimate, the continuous Chernoff derivation, novelty,
or the computational/provenance statements in the report.

## Verification

`Verify.ps1` rebuilds the public import graph, checks the listed statements,
and inspects their transitive axioms. Only propext, Classical.choice, and
Quot.sound are accepted. It also scans all project and vendored Lean sources
for unfinished proofs and custom axioms, and hashes the exact source set.
The expected audit inventory is now read from `Audit.lean`, so adding results
cannot silently leave the former fixed nine-result count in place. A failed
or interrupted verification cannot leave a stale `passed` status.

The current run's outcome and complete inventory are in
`../verification/result.json`; proof logs are alongside that file.

**Final run: PASS, 2026-09-07 18:12:28 UTC.** The full 3358-job build
completed successfully. All 32 axiom inventories contained only the accepted
Lean foundations, and the source scan found no unfinished proofs or custom
axioms. The manifest records 119 source/configuration files.
