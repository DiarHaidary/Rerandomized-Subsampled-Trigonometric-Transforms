# A finite Jensen reduction for exact-size row sampling

Date: 2026-09-07. Mathematical argument audited independently by a second
AI agent. Lean implementation is in progress; this note is not a Lean certificate.

Let n>=2 and 1<=M<n, p=M/n, and let B be an iid Bernoulli(p) row subset,
with K=|B|. Couple B to a uniform M-subset T so that the two sets are nested.
The joint law is invariant under row permutations. Such a law can be realized
by uniform fill/thin, or by an independent uniform permutation applied to
prefixes of lengths K and M.

Write a=E(K-M)_+=E(M-K)_+. Independence of K from T follows from the uniform
M-subset marginal conditional on each K. Permutation symmetry and nesting give

    P(i in B | T) = 1-a/M              for i in T,
    P(i in B | T) = a/(n-M)            for i outside T.

For any deterministic symmetric matrices A_i with sum A_i=I, define

    E_B=(1/p) sum_(i in B) A_i-I,
    E_T=(n/M) sum_(i in T) A_i-I.

Then exactly

    E[E_B | T] = c E_T,
    c=1-a/v,    v=M(n-M)/n.

Here v=Var K>=1/2. Since E(K-M)=0, 2a=E|K-M|. Cauchy-Schwarz gives
a^2<=v/4. For v>=1/2, sqrt(v)/2 <=3v/4, so c>=1/4.

The function A -> tr(A^(2q)) is convex on real symmetric matrices. Conditional
Jensen and homogeneity therefore imply

    E tr(E_T^(2q)) <= 4^(2q) E tr(E_B^(2q)).

The coupling is independent of both sign families. It applies pointwise to the
SRHT row effects A_i=w_i w_i^T, then averages over the sign laws. Thus no
binomial exponential-tail bound or continuous uniform variables are needed.

If M>=8192 D/epsilon^2 and 0<epsilon<=1, the Bernoulli envelope from the draft
satisfies

    4[6 sqrt(D/M)+9D/M] < epsilon/2.

The same q as the draft makes the fixed-size failure at most delta/4, hence
at most delta. The endpoint M=n is handled by exact orthogonality.

This comparison uses symmetric matrices summing to I; positivity is not
needed in the Jensen step. The SRHT operator proof still needs its full
positive shared-factor argument to supply the Bernoulli moment estimate.
