# Correspondence with Problem 5.6

The problem source is Amsel et al., *Linear Systems and Eigenvalue Problems:
Open Questions from a Simons Workshop*, [arXiv:2602.05394v3](https://arxiv.org/pdf/2602.05394v3),
Definitions 5.1 and 5.3 and Problem 5.6, printed pages 37 and 41–42.
Section 5.3 credits Ethan N. Epperly as scribe. The source poses the problem;
the proof formalized here is the project's [technical report](../docs/SRHT_Technical_Report.md),
revised 7 September 2026. These are separate provenance entries in
[`formalization.yaml`](../formalization.yaml).

## Same transform and success event

Definition 5.3 specifies the real rerandomized Walsh transform

    Ω = sqrt(n/M) D₁ H D₂ H S,

where the source calls the sample size `k`; this account uses `M` to avoid
confusion with the exponent in the formal ambient size `n = 2^k`.
The source applies `Ωᵀ` to vectors. Since `Hᵀ = H` and diagonal sign
matrices are symmetric, the actual map formalized here is

    Ωᵀ = sqrt(n/M) R H D_y H D_x,     R = Sᵀ.

Definition 5.1 measures injectivity and dilation using **squared** Euclidean
norms. The formal event uses precisely those quantities. Problem 5.6 asks for
sample size `O(r/ε²)` and factors `1−ε`, `1+ε`, with the stated ambient-size
condition `n = Ω(log r)`.

The following details describe the formal statement and its connection to the
concrete proof, rather than additional assertions from the problem collection.

| Mathematical object | Formal meaning |
|---|---|
| Ambient space | Real coordinates indexed by `Fin k → ZMod 2`, of cardinality `2^k`. |
| Walsh transform | The normalized real character matrix, with entries `±1/sqrt(2^k)` and proved orthogonality. |
| Sign diagonals | Two mutually independent assignments of independent uniform bits, mapped to `±1`. |
| Sampling | A uniformly chosen subset of exactly `M` coordinates, independent of both sign assignments. Rows are distinct. |
| Input subspace | An arbitrary fixed real `2^k`-by-`d` matrix `U` with `UᵀU = I`; its columns are an orthonormal basis for the subspace. |
| Success | For every coefficient vector `v`, `(1−ε)||v||² ≤ ||ΩᵀUv||² ≤ (1+ε)||v||²`. Since `U` is isometric, this is norm preservation throughout its column space. |
| Probability | The literal finite counting/product law of the two sign assignments and the row subset. It is independent of `U`. |

Representing the subspace by an arbitrary orthonormal frame does not impose an
incoherence or coordinate-support restriction. The single success event
quantifies over every vector in the frame's column space; it is not only a
fixed-vector estimate. The theorem quantifies over every fixed frame, while
the sampling distribution depends on dimensions and error parameters only.
It does not assert that a single draw succeeds simultaneously on all possible
subspaces.

## Exact dimension and confidence claim

For `1 ≤ d ≤ n`, `0 < ε < 1`, and `0 < δ < 1/2`, define

    q = ceil(log(4d/δ) / log 4)
    M = min(n, ceil(8192 (d + 27q³) / ε²)).

The compared declaration `RerandomizedSTT.problem_5_6` states all of:

1. `1 ≤ M ≤ n`;
2. `M ≤ [8192(1+432/δ)+1] d/ε²`;
3. success probability at least `1−δ` for the simultaneous squared-norm event.

For a chosen constant failure probability, for example `δ = 1/4`, the
coefficient in the second inequality is the fixed numerical constant
`14163969`. This gives `O(d/ε²)` with a constant independent of ambient size,
subspace dimension, and distortion. The ambient cap includes the case where
every row is retained; that case is an exact isometry for every sign draw.
The formal theorem does not require an extra lower bound on the ratio of
ambient size to subspace dimension. In particular, its explicit `d ≤ n`
domain covers the ambient-size regime in the posed problem.

The full library proves the stronger joint estimate

    M ≤ min(n, 110592001 [d + log³(1/δ)] / ε²)

and genuine limited-independence variants. Their names and exact report
correspondence are in [`REPORT_COVERAGE.md`](REPORT_COVERAGE.md). They remain
complete library theorems, but the current Comparator configuration selects
only `RerandomizedSTT.problem_5_6`, which uses fully independent signs and the
displayed dimension-linear bound. A Comparator certificate for that selection
must not be described as a separate comparison of all 32 audited endpoints.

## Scope and evidence

This is the Walsh model in Definition 5.3, on real spaces of power-of-two
ambient dimension. The title does not enlarge the theorem to complex Fourier
transforms, cosine transforms, or all orthogonal transforms with bounded
entries. The development does not verify a bit-level sampler, a fast-transform
implementation, or an operation-count theorem.

The constant-failure interpretation is essential to the dimension-linear
statement. Its displayed constant depends on `δ`. A universal
`O(ε⁻²[d + log(1/δ)])` confidence bound is not claimed. The accompanying proof
library in fact contains explicit support-alignment obstructions to such a
bound for a fixed number of rounds, including two rounds. Those results are
outside this Comparator selection.

The original verified source snapshot has a build and 32 standard-axiom
audits recorded on 7 September 2026. Packaging this proof for a new statement
surface adds a distinct correspondence check: Comparator must confirm that
the completed `Solution` proves the declaration exposed in `Challenge`, and
the Palomar verification process additionally uses NanoDa. The inherited
build record alone does not certify those new checks. Consult the current
verification output and the exact repository commit when reporting their
status.

Lean verification concerns the formal propositions and proof terms. The
comparison above is a disclosed source interpretation; it does not establish
novelty, priority, source-author endorsement, independent human peer review,
or Palomar registration.
