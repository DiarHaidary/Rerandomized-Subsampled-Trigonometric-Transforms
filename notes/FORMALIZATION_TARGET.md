# Completion requirements

The original finite core target was completed and kernel-verified on
2026-09-07. Following the user's supplied audit, the target now also includes
the principal results and Appendix A of the consolidated technical report.
The public import is ../SRHT.lean. ../verification/result.json records the
current full build, named axiom audits, and source scan.

The reference texts are ../../ChatGPT/notes/session5_full_moment_theorem.md
and ../../ChatGPT/SRHT_Technical_Report.tex. The final results must not assume
their operator or moment bounds.

For every Walsh order n=2^k, every real n-by-d frame U with transpose(U) U=I,
1<=d<=n, 0<epsilon<1, and 0<delta<1/2, set
q=ceil(log(4d/delta)/(2 log 2)), D=d+27q^3, and
M=min(n,ceil(8192 D/epsilon^2)).

The endpoint must bound by delta the probability that the L2 operator norm
of the actual sampled two-round Gram minus I exceeds epsilon. The sample
must be uniform over distinct M-element row subsets, independently of both
sign families. Both sign families may have only min(n,4q)-wise independence.
The M=n and k=0 endpoints must be included.

Completion also requires:

- actual Walsh character matrix, actual signs, and actual probability weights;
- the full quantitative small-row estimate, with its five-term norm proof;
- the positive selector estimate and its actual matrix specialization;
- exact probability/operator correspondence and the reachable-degree cutoff;
- exact moment transfer under limited independence;
- a proved reduction to the fixed-size sampling law;
- finite parameter arithmetic and the full O((d+log³(1/delta))/epsilon²) row order;
- arbitrary real Bernoulli rates and the composed limited-independence bound;
- Appendix A's actual alignment events, exact row-miss probabilities,
  necessary row inequality, stronger two-round event, and quantified
  impossibility of a uniform logarithmic confidence budget;
- a compiled unconditional endpoint and its printed transitive axiom inventory.

Standard Lean foundational axioms are permitted. No sorryAx, custom mathematical
axioms, assumed hard estimates, opaque conjectural constants, or vacuous model
definitions are permitted. Compiled helper modules are not completion.

The finite Jensen coupling described in finite_jensen_sampling.md is a
mathematically audited alternative to the draft's continuous-priority coupling.
It proves the same final sampling theorem with the same conservative constants.
See REPORT_COVERAGE.md for exact theorem names and which intermediate
derivations are intentionally replaced by alternative proofs.
