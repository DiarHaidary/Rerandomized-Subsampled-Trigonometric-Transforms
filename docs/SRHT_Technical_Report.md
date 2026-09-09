# Two-round Walsh SRHT: a self-contained moment and embedding proof

Technical research report | 7 September 2026

Prepared for the SRHT project. This revision presents the operator estimates and finite sampling argument used by the accompanying Lean formalization. The main embedding and Bernoulli theorems, the quantitative row bound, and Appendix A's conclusions have been checked in Lean 4.33.0. The complete build and 32 transitive-axiom audits passed on 7 September 2026, using only Lean's standard foundations. Section 12 distinguishes this verification from the report's exposition and finite computational checks. No publication-priority claim is made.

## Abstract

Let \(H\) be the normalized Walsh-Hadamard matrix of order \(n\), let \(D_x,D_y\) be independent diagonal sign matrices, and sample \(M\) distinct rows uniformly from \(HD_yHD_x\). For every fixed real \(d\)-dimensional subspace, we prove a squared-norm embedding guarantee with failure probability at most \(\delta\) using

$$
M=\min\left\{n,\left\lceil8192\epsilon^{-2}(d+27q^3)\right\rceil\right\},
\qquad
q=\left\lceil\frac{\log(4d/\delta)}{2\log2}\right\rceil .
\tag{A}
$$

Each sign family needs only \(\min(n,4q)\)-wise independence. The resulting row order is \(O(\epsilon^{-2}[d+\log^3(1/\delta)])\), capped at \(n\), and is \(O(d/\epsilon^2)\) at fixed failure probability, uniformly over all Walsh orders and subspace dimensions. The central estimate is an even trace-moment bound for Bernoulli row sampling. Its proof uses the exact finite-product multiplication representation, a restricted-row normal-ordering identity, and a weighted positive-operator inequality for selector creation. All three are developed below. A finite nested coupling and conditional Jensen inequality convert the Bernoulli moment to a fixed-size moment with a factor of four in its root. An appendix gives the support-alignment obstruction that explains why a uniform Gaussian confidence term cannot be expected from a fixed number of these mixing rounds.

## 1. Model, notation, and main statements

### 1.1 Walsh normalization and the embedding event

Let \(n=2^k\), with \(k\ge0\), and index coordinates by the additive group \(G=\mathbb F_2^k\). Addition of indices always means addition in this group. Write

$$
\chi_b(a)=(-1)^{a\cdot b},\qquad
H_{ab}=\frac{\chi_b(a)}{\sqrt n},\qquad
f_b(a)=\frac{\chi_b(a)}{\sqrt n}.
\tag{1.1}
$$

The character identity \(\chi_b(a)\chi_c(a)=\chi_{b+c}(a)\) and cancellation of every nontrivial character give

$$
\sum_{a\in G}\chi_b(a)\chi_c(a)=n\,\mathbf1_{\{b=c\}}.
\tag{1.2}
$$

Indeed, if \(b+c\ne0\), choose a coordinate on which it is nonzero and pair each \(a\) with the vector obtained by flipping that coordinate. The paired summands cancel. Consequently \(H^\top H=H^2=I_n\), and \((f_b)_{b\in G}\) is an orthonormal basis.

Fix \(U\in\mathbb R^{n\times d}\), where \(1\le d\le n\) and \(U^\top U=I_d\). Define

$$
u_i=U^\top e_i,\qquad P=UU^\top,\qquad
\ell_i=\|u_i\|^2=P_{ii},\qquad
\mu=\max_i\ell_i .
\tag{1.3}
$$

Thus \(P=P^\top=P^2\), \(0\le\mu\le1\), \(\sum_i\ell_i=d\), and \(\sum_i u_i u_i^\top=I_d\). We use the uniform leverage bound \(\ell_i\le1\); no improvement depending on the actual value of \(\mu\) is required. Replacing \(\mu\) by its upper bound one imposes no extra condition on the frame. All norms of operators or matrices below are Euclidean operator norms; \(\operatorname{tr}\) is the usual unnormalized trace. The notation \(A\preceq B\) means that \(B-A\) is positive semidefinite.

Let \(x=(x_i)\) and \(y=(y_a)\) be sign families and put

$$
W=HD_yHD_xU,\qquad w_j=W^\top e_j,\qquad
\sum_j w_jw_j^\top=W^\top W=I_d .
\tag{1.4}
$$

The last equality holds for every realization of the signs. Let \(R\) select a uniform \(M\)-element subset of rows, in any fixed ordering of that subset, independently of both sign families. The sketch and its subspace Gram are

$$
S=\sqrt{\frac nM}\,RHD_yHD_x,\qquad
U^\top S^\top SU=\frac nM\sum_{j\in T_M}w_jw_j^\top .
\tag{1.5}
$$

The event \(\|U^\top S^\top SU-I_d\|\le\epsilon\) is equivalent to

$$
(1-\epsilon)\|z\|^2\le\|SUz\|^2\le(1+\epsilon)\|z\|^2
\quad\hbox{for every }z\in\mathbb R^d .
\tag{1.6}
$$

This is a statement for each fixed subspace chosen before the sketch randomness. It does not assert one sampled sketch works simultaneously for all subspaces.

### 1.2 Fixed-size theorem

**Theorem 1.** Fix \(0<\epsilon<1\) and \(0<\delta<1/2\). Define \(q\) as in (A), \(D_q=d+27q^3\), and \(M=\min(n,\lceil8192D_q/\epsilon^2\rceil)\). Suppose each sign family is unbiased and \(\min(n,4q)\)-wise independent, and the two families and the uniform row subset are mutually independent. Then

$$
\mathbb P\!\left\{\|U^\top S^\top SU-I_d\|>\epsilon\right\}\le\delta .
\tag{1.7}
$$

There is no additional relation between \(n\) and \(d\). When \(M=n\), the Gram is exactly \(I_d\); in particular the case \(n=1\) is deterministic. The explicit constants are conservative proof constants.

### 1.3 Bernoulli moment theorem

For \(0<\rho<1\), let \(\eta_j\) be independent Bernoulli variables of mean \(\rho\), independent of the signs. Set \(m=\rho n\), an expected sample size that need not be an integer, and define

$$
E_\rho=\frac1\rho\sum_j\eta_jw_jw_j^\top-I_d
       =\sum_j\left(\frac{\eta_j}{\rho}-1\right)w_jw_j^\top .
\tag{1.8}
$$

**Theorem 2.** Under the fully independent product law, for every integer \(q\ge1\),

$$
\mathbb E\operatorname{tr}(E_\rho^{\,2q})
\le d\left[
6\sqrt{\frac{d+27q^3}{m}}+
9\frac{d+27q^3}{m}
\right]^{2q}.
\tag{1.9}
$$

The same inequality holds when the two sign families are only \(\min(n,4q)\)-wise independent and the selector family is only \(\min(n,2q)\)-wise independent with the same Bernoulli marginals, provided the three families remain mutually independent. At \(\rho=1\), \(E_\rho=0\).

The proof proceeds in the following order: product-space algebra; linear row bounds; a small-subset row-Gram bound; positive selector control; exact vacuum moments; limited independence; and fixed-size sampling.

## 2. Finite-product Hilbert spaces and local operators

### 2.1 Sign monomials as an orthonormal occupation basis

Under independent unbiased signs, the monomials \(x_A=\prod_{i\in A}x_i\), for \(A\subseteq G\), form an orthonormal basis of the real \(L^2\) space. In fact, \(x_Ax_B=x_{A\mathbin{\triangle}B}\), whose expectation is zero unless \(A=B\). Identify \(x_A\) with a basis vector \(|A\rangle\). Let \(\mathcal X_r\) be the span of subsets of size \(r\); define the second-sign spaces \(\mathcal Y_s\) in the same way.

On a single occupation space define annihilation, creation, and occupancy by

$$
\begin{aligned}
a_i|A\rangle&=\mathbf1_{\{i\in A\}}|A\setminus\{i\}\rangle,\\
a_i^\dagger|A\rangle&=\mathbf1_{\{i\notin A\}}|A\cup\{i\}\rangle,\\
N_i|A\rangle&=\mathbf1_{\{i\in A\}}|A\rangle .
\end{aligned}
\tag{2.1}
$$

Operators at different sites commute. Direct evaluation on the two local states gives

$$
a_i^\dagger a_i=N_i,\qquad
a_i a_i^\dagger=I-N_i,\qquad
a_i a_l^\dagger=a_l^\dagger a_i+
\mathbf1_{\{i=l\}}(I-2N_i).
\tag{2.2}
$$

There are no fermionic signs. Multiplication by \(x_i\) toggles the presence of \(i\), so its exact operator is \(a_{x,i}+a_{x,i}^\dagger\). For a real vector \(f\in\mathbb R^n\), write \(a(f)=\sum_i f(i)a_i\), and similarly for creation. By bilinearity,

$$
a(f)a(g)^\dagger
=a(g)^\dagger a(f)+\langle f,g\rangle I
-2\sum_i f(i)g(i)N_i .
\tag{2.3}
$$

In particular, for Walsh vectors,

$$
a_y(f_b)a_y(f_c)^\dagger
=a_y(f_c)^\dagger a_y(f_b)
+\mathbf1_{\{b=c\}}I-\frac2n\sum_a\chi_{b+c}(a)N_{y,a}.
\tag{2.4}
$$

### 2.2 Extraction, insertion, and their exact norm factors

For grade \(r\), define an extraction map by

$$
\mathcal E_r|A\rangle=\sum_{i\in A}e_i\otimes|A\setminus\{i\}\rangle
:\mathcal X_r\longrightarrow\mathbb R^n\otimes\mathcal X_{r-1}.
\tag{2.5}
$$

Distinct input subsets have disjoint supports in the output basis, and each input produces \(r\) orthogonal terms. Thus \(\mathcal E_r^\dagger\mathcal E_r=rI\) and \(\|\mathcal E_r\|\le\sqrt r\), with equality when the grade-\(r\) space is nonzero. The adjoint \(\mathcal E_{r+1}^\dagger\) inserts a site, annihilating attempts to insert an already occupied site; its norm is at most \(\sqrt{r+1}\), with equality when grade \(r+1\) is nonzero. These upper bounds also cover empty grade spaces. The grade-zero extraction is zero. At the top grade, a creation map is zero.

### 2.3 One-particle operators and hard-core lifts

For a one-particle matrix \(B=(B_{li})\), define its lift to grade \(r\) by

$$
\mathrm d\Gamma_r(B)=\sum_{l,i}B_{li}a_l^\dagger a_i .
\tag{2.6}
$$

To justify the bounds used later, identify \(|A\rangle\), for \(A=\{i_1,\ldots,i_r\}\), with the normalized symmetric tensor

$$
J_r|A\rangle=
\frac1{\sqrt{r!}}\sum_{\pi\in\mathfrak S_r}
e_{i_{\pi(1)}}\otimes\cdots\otimes e_{i_{\pi(r)}}.
\tag{2.7}
$$

The vectors on the right are orthonormal as \(A\) varies. Compressing \(\sum_{\nu=1}^r B^{(\nu)}\) by this isometry gives exactly (2.6): an off-diagonal entry replaces one occupied site by another absent site with coefficient \(B_{li}\), while a diagonal entry contributes \(B_{ii}\) once for each occupied \(i\). Repeated-site outputs are removed by compression.

It follows that

$$
\|\mathrm d\Gamma_r(B)\|\le r\|B\|,\qquad
0\preceq B\preceq bI\ \Longrightarrow\
0\preceq\mathrm d\Gamma_r(B)\preceq rbI .
\tag{2.8}
$$

These assertions also hold for a one-particle operator acting jointly with an auxiliary row register: apply it to that register and one labeled particle at a time, sum over the particle slots, and compress. With two separate particle species of grades \(r,s\), a joint row/one-\(x\)/one-\(y\) kernel \(K\) has a double lift of norm at most \(rs\|K\|\). This follows by summing \(rs\) operators, one for each ordered pair of particle slots, before compression. For the separable matrix entries used below, the lift is precisely the corresponding product \(a_{x,l}^\dagger a_{x,i}a_y(g)^\dagger a_y(f)\).

### 2.4 Biased selector sites

For a Bernoulli variable \(\eta\) of mean \(\rho\), the local orthonormal basis is

$$
|0\rangle=1,\qquad
|1\rangle=\frac{\eta-\rho}{\sqrt{\rho(1-\rho)}}.
\tag{2.9}
$$

Let \(b=\eta/\rho-1\). Its constant-to-constant matrix entry is zero. Its off-diagonal entry is \(\mathbb E[b|1\rangle]=\sqrt{(1-\rho)/\rho}\). Since

$$
\mathbb E(\eta-\rho)^3=\rho(1-\rho)(1-2\rho),
\tag{2.10}
$$

the remaining diagonal entry is \((1-2\rho)/\rho\). Therefore multiplication by \(b\) is exactly

$$
\begin{pmatrix}0&\sigma\\ \sigma&\tau\end{pmatrix}
=\sigma(c^\dagger+c)+\tau N,
\qquad
\sigma=\sqrt{\frac{1-\rho}{\rho}},\quad
\tau=\frac{1-2\rho}{\rho}.
\tag{2.11}
$$

Here \(c^\dagger,c,N\) are the same two-state creation, annihilation, and occupancy matrices as in (2.1). Products of the local basis vectors form an orthonormal basis for independent selectors; let \(\mathcal Z_t\) denote selector degree \(t\). Degree records a polynomial basis state, not the number of rows in an actual sampled realization.

## 3. Linear row factorization

### 3.1 Exact row functional and four grade transitions

We use the Walsh normalization and the isometric input frame from Section 1. In particular, \(P=UU^\top\) satisfies \(\|P\|\le1\), its diagonal entries obey \(0\le\ell_i\le1\), and \(\sum_i\ell_i=d\). All estimates in Sections 3--5 use this universal bound on the leverage scores.

Expanding both Walsh matrices gives the exact row identity
$$
w_j^\top
=\frac1n\sum_{a,i}\chi_j(a)\chi_i(a)y_a x_i u_i^\top
=\frac1{\sqrt n}\sum_i u_i^\top X_iY(f_{j+i}),
\tag{3.1}
$$
where \(X_i\) is multiplication by \(x_i\), and \(Y(f)=\sum_a f(a)y_a\) is multiplication by that linear form. Each row channel includes the common factor \(n^{-1/2}\); Section 4 removes it explicitly when defining the unnormalized collected map. Under the occupation-basis identification in Section 2, \(X_i=a_{x,i}^\dagger+a_{x,i}\) and \(Y(f)=a_y(f)^\dagger+a_y(f)\).

For fixed input sign grades \(r,s\), write
$$
\mathcal H_{r,s}=\mathbb R^d\otimes\mathcal X_r\otimes\mathcal Y_s,
\qquad \Pi_{r,s}=\text{the orthogonal projection onto }\mathcal H_{r,s}.
\tag{3.2}
$$
Let \(T_j^{\alpha\beta}\), for \(\alpha,\beta\in\{+,-\}\), be the restriction of the corresponding term of (3.1) to \(\mathcal H_{r,s}\), with \(+\) denoting creation and \(-\) annihilation. For example,
$$
T_j^{--}=\frac1{\sqrt n}\sum_i u_i^\top a_{x,i}a_y(f_{j+i})\Pi_{r,s}.
$$
The four output grades are \((r+1,s+1),(r+1,s-1),(r-1,s+1),(r-1,s-1)\). Any transition to an invalid grade is zero. Their output spaces are mutually orthogonal, so all cross-products between distinct channels vanish. Consequently
$$
\Pi_{r,s}M_{w_jw_j^\top}\Pi_{r,s}
=\sum_{\alpha,\beta\in\{+,-\}}
(T_j^{\alpha\beta})^\dagger T_j^{\alpha\beta}.
\tag{3.3}
$$
Here \(M_F\) denotes multiplication by the matrix-valued function \(F\). Thus (3.3) concerns the actual row multiplication operator, represented in the finite occupation basis.

### 3.2 Three coefficient flattenings

For a fixed row \(j\), consider the coefficient tensor
$$
C_j=\sum_i u_i^\top\otimes e_i\otimes f_{j+i}.
\tag{3.4}
$$
Its flattening \(F_j:\mathbb R^d\to\mathbb R^n\otimes\mathbb R^n\) sends \(z\) to \(\sum_i\langle u_i,z\rangle e_i\otimes f_{j+i}\). Orthogonality and \(U^\top U=I_d\) give
$$
\|F_jz\|^2=\sum_i|\langle u_i,z\rangle|^2=\|z\|^2.
\tag{3.5}
$$
For the flattening from the external and \(y\) factors to the \(x\) factor, express the input uniquely as \(\sum_i z_i\otimes f_{j+i}\). The output is \(\sum_i\langle u_i,z_i\rangle e_i\), and
$$
\sum_i|\langle u_i,z_i\rangle|^2
\le\sum_i\ell_i\|z_i\|^2
\le\sum_i\|z_i\|^2.
\tag{3.6}
$$
The flattening from the external and \(x\) factors to the \(y\) factor is also a contraction: write the input in the basis \((e_i)\) and use the orthonormality of \((f_{j+i})\) in the same calculation.

For the \(++\) channel, apply \(F_j\), then insert its two one-particle outputs into the sign occupations. The insertion norms from Section 2.2 are at most \(\sqrt{r+1}\) and \(\sqrt{s+1}\). For the \(+-\) channel, extract one \(y\) site, apply the second flattening, and insert one \(x\) site. Its two occupation factors are bounded by \(\sqrt s\) and \(\sqrt{r+1}\). Exchanging the two species gives the \(-+\) channel. Restoring the common scalar in (3.1),
$$
\begin{aligned}
\|T_j^{++}\|^2&\le\frac{(r+1)(s+1)}n,\\
\|T_j^{+-}\|^2&\le\frac{(r+1)s}n,\\
\|T_j^{-+}\|^2&\le\frac{r(s+1)}n.
\end{aligned}
\tag{3.7}
$$
These bounds remain valid at grade zero and at the top grade, because a forbidden extraction or insertion is the zero map.

### 3.3 Collecting the orthogonal channels

Set
$$
a_{r,s}=(r+1)(s+1)+(r+1)s+r(s+1)
=3rs+2r+2s+1.
\tag{3.8}
$$
Let \(\mathcal B_j\) be the sum of the three channel Grams in (3.3) other than double annihilation. Each Gram is positive, and (3.7) gives
$$
0\preceq\mathcal B_j\preceq\frac{a_{r,s}}n I.
\tag{3.9}
$$
For a deterministic set of row labels \(T\subseteq G\), with \(t=|T|\), define
$$
K_T=\sum_{j\in T}M_{w_jw_j^\top},
\qquad
\mathcal R_Tz=\sum_{j\in T}e_j\otimes T_j^{--}z.
\tag{3.10}
$$
The identity \(W^\top W=I_d\), which holds for every sign realization, implies \(0\preceq K_T\preceq I\). Summing the exact orthogonal-channel identity yields
$$
\begin{aligned}
\Pi_{r,s}K_T\Pi_{r,s}
&=\mathcal R_T^\dagger\mathcal R_T+\sum_{j\in T}\mathcal B_j,\\
\|\Pi_{r,s}K_T\Pi_{r,s}\|
&\le\|\mathcal R_T\|^2+\frac{t a_{r,s}}n.
\end{aligned}
\tag{3.11}
$$
Equivalently, one can first collect each of the four channels over \(T\), use their orthogonal output grades to eliminate all cross-products, and then sum the four Gram norms. Both expressions give (3.11). It remains to control the double-annihilation channel collectively over the row set.

## 4. Restricted double annihilation: the complete five-term derivation

### 4.1 Collected Gram and normal-ordering expansion

Assume first that \(r,s\ge1\), and put \(p=r-1\) and \(v=s-1\). These are the output grades of double annihilation; \(t=|T|\) continues to denote the number of selected row labels. Define the unnormalized collected map on the full sign spaces by
$$
(\mathcal A_Tz)_j=\sum_i u_i^\top a_{x,i}a_y(f_{j+i})z,
\qquad j\in T.
$$
Thus \(\mathcal R_T=n^{-1/2}\mathcal A_T\Pi_{r,s}\). Its uncompressed row Gram \(\mathcal G_T=\mathcal A_T\mathcal A_T^\dagger\) has blocks
$$
(\mathcal G_T)_{jk}
=\sum_{i,l}P_{il}\,
a_{x,i}a_{x,l}^\dagger\,
a_y(f_{j+i})a_y(f_{k+l})^\dagger,
\qquad j,k\in T.
\tag{4.1}
$$
Let \(Q_{p,v}\) be the projection onto \(\mathbb R^T\otimes\mathcal X_p\otimes\mathcal Y_v\). Double annihilation has the exact grade transition \((r,s)\mapsto(p,v)\). Therefore
$$
\mathcal A_T\Pi_{r,s}=Q_{p,v}\mathcal A_T\Pi_{r,s},
\qquad
n\|\mathcal R_T\|^2
\le\|Q_{p,v}\mathcal A_T\|^2
=\|Q_{p,v}\mathcal G_TQ_{p,v}\|.
$$
This compression inequality is sufficient for the proof and keeps the input and output projections explicit.

Introduce \(S_i=I-2N_{x,i}\) and
$$
\Delta_{bc}=\mathbf1_{\{b=c\}}I-
\frac2n\sum_a\chi_{b+c}(a)N_{y,a}.
\tag{4.2}
$$
The commutation identities (2.2) and (2.4) expand each row block of (4.1) as
$$
\sum_{i,l}P_{il}
\big(a_{x,l}^\dagger a_{x,i}+\mathbf1_{\{i=l\}}S_i\big)
\big(a_y(f_{k+l})^\dagger a_y(f_{j+i})+\Delta_{j+i,k+l}\big).
\tag{4.3}
$$
The product of the two normally ordered factors is \(\mathcal M\); the \(x\) commutator times the normally ordered \(y\) factor is \(\mathcal Y\); and the normally ordered \(x\) factor times \(\Delta\) splits into \(\mathcal X-\mathcal F\). The product of the commutators is \(\mathcal E_0\). In the next subsections, these symbols denote the corresponding operators restricted to the output grades \(p,v\). Every term preserves those two grades, and the exact identity is
$$
Q_{p,v}\mathcal G_TQ_{p,v}
=\mathcal E_0+\mathcal X-\mathcal F+\mathcal Y+\mathcal M.
\tag{4.4}
$$
We bound the norm of each of these five terms, including the correction \(\mathcal F\) that appears with a minus sign.

### 4.2 The grouped double commutator

Let \(L_x=\sum_i\ell_iN_{x,i}\), so \(0\preceq L_x\preceq dI\). Since \(i=l\) in the product of the two commutators, \(\chi_{j+i+k+i}(a)=\chi_{j+k}(a)\), and its row blocks are
$$
(\mathcal E_0)_{jk}
=(dI-2L_x)\left[
\mathbf1_{\{j=k\}}I-\frac2n\sum_a\chi_{j+k}(a)N_{y,a}
\right].
\tag{4.5}
$$
On the full row register define
$$
Q=\sum_a |f_a\rangle\langle f_a|_{\rm row}\otimes N_{y,a}.
\tag{4.6}
$$
The Walsh vectors are orthonormal and the occupancy operators are projections, so \(Q^2=Q=Q^\dagger\). Its compression \(Q_T\) to row labels in \(T\) satisfies \(0\preceq Q_T\preceq I\). Its row block \(j,k\) is \(n^{-1}\sum_a\chi_{j+k}(a)N_{y,a}\). Hence
$$
\mathcal E_0=(dI-2L_x)(I-2Q_T),
\qquad \|\mathcal E_0\|\le d.
\tag{4.7}
$$
The factors act on separate \(x\) and row/\(y\) registers and commute. Their spectral intervals lie in \([-d,d]\) and \([-1,1]\). Equivalently, on a fixed pair of occupation subsets the first factor is the scalar \(\sum_i\ell_i(1-2\mathbf1_{\{i\in A\}})\), whose absolute value is at most \(d\), while the second factor is a compression of a Walsh-conjugated diagonal sign matrix. Thus grade compression introduces no additional norm factor.

### 4.3 The \(x\)-transfer term

The identity part of the \(y\) commutator contributes
$$
\mathcal X_{jk}
=\sum_{i,l}P_{il}\mathbf1_{\{j+i=k+l\}}
a_{x,l}^\dagger a_{x,i}.
\tag{4.8}
$$
Its row/one-particle kernel is
$$
\mathsf X_{jk}
=\sum_{i,l}P_{il}\mathbf1_{\{j+i=k+l\}}
|l\rangle\langle i|.
\tag{4.9}
$$
First allow all row labels in \(G\). Fourier transformation of the row register gives
$$
\frac1n\sum_{j,k}\chi_a(j)\chi_b(k)
\mathbf1_{\{j+i=k+l\}}
=\mathbf1_{\{a=b\}}\chi_a(i+l).
\tag{4.10}
$$
Indeed, substitute \(k=j+i+l\) and apply character orthogonality. With \(D_a=\operatorname{diag}(\chi_a(i))\), the frequency-\(a\) block is \(D_aPD_a\), of norm at most one. Restriction to \(T\) is an orthogonal compression, so the restricted kernel is also a contraction. Its lift to the \(p\) occupied \(x\) slots has norm at most \(p\) by Section 2.3:
$$
\|\mathsf X\|\le1,
\qquad \|\mathcal X\|\le p.
\tag{4.11}
$$
The second sign register is a spectator in this estimate.

### 4.4 Bounding the correction term in norm

The remaining part of the \(y\) commutator gives the correction
$$
\mathcal F=\frac2n\sum_a
\big[\chi_{j+k}(a)\big]_{j,k\in T}
\otimes\mathrm d\Gamma_p(D_aPD_a)\otimes N_{y,a}.
\tag{4.12}
$$
This formula follows by separating \(\chi_{j+i+k+l}(a)\) into \(\chi_{j+k}(a)\chi_i(a)\chi_l(a)\). To estimate its norm, first replace the lifted operator in (4.12) by the one-particle matrix \(D_aPD_a\), and allow all row labels. The resulting kernel on the row, one-\(x\)-particle, and full \(y\)-occupation registers is
$$
\mathsf F_{\rm full}
=2\sum_a |f_a\rangle\langle f_a|_{\rm row}
\otimes D_aPD_a\otimes N_{y,a}.
$$
Fourier transformation of the row register makes this operator a direct sum of the blocks \(2D_aPD_a\otimes N_{y,a}\). Each block has norm at most two, because \(\|P\|\le1\) and \(\|N_{y,a}\|\le1\). Row restriction cannot increase this norm. Applying the single-particle lift on grade \(p\), with the row and \(y\)-occupation registers retained as auxiliary factors, gives
$$
\|\mathsf F\|\le2,
\qquad \boxed{\|\mathcal F\|\le2p.}
\tag{4.13}
$$
In the norm estimate for (4.4), the term \(-\mathcal F\) therefore contributes \(2p\). This is the correction-term estimate used in the verified proof.

### 4.5 The \(y\)-transfer term with its full \(x\) commutator

The next term is
$$
\mathcal Y_{jk}
=\sum_i\ell_i S_i\otimes
a_y(f_{k+i})^\dagger a_y(f_{j+i}).
\tag{4.14}
$$
Each \(S_i=I-2N_{x,i}\) is a self-adjoint unitary and commutes with the \(y\) operators. For \(\psi=(\psi_j)_{j\in T}\) in the output-grade space, moving one annihilator to each side gives
$$
\langle\psi,\mathcal Y\psi\rangle
=\sum_{i,j,k}\ell_i
\left\langle a_y(f_{k+i})\psi_j,
S_i a_y(f_{j+i})\psi_k\right\rangle.
\tag{4.15}
$$
Apply Cauchy--Schwarz to the complete sum over \((i,j,k)\), with weights \(\ell_i\). The two sums of squared norms agree after exchanging \(j,k\), since \(S_i\) is unitary. Thus
$$
|\langle\psi,\mathcal Y\psi\rangle|
\le\sum_j\left\langle\psi_j,
\mathrm d\Gamma_v(G_T)\psi_j\right\rangle,
\qquad
G_T=\sum_i\ell_i\sum_{k\in T}|f_{k+i}\rangle\langle f_{k+i}|.
\tag{4.16}
$$
For each fixed \(k\), the vectors \(f_{k+i}\) form an orthonormal basis as \(i\) varies. Since \(\ell_i\le1\), the corresponding weighted sum of rank-one projections is at most \(I\). It follows that \(0\preceq G_T\preceq tI\). The lift on grade \(v\) has norm at most \(tv\). Also, \(\mathcal Y\) is self-adjoint, as is seen by transposing its row blocks and exchanging \(j,k\). Hence
$$
\|\mathcal Y\|\le tv.
\tag{4.17}
$$
The full commutator \(S_i\), of norm one, is retained throughout this estimate.

### 4.6 The mixed kernel is a contraction

The fully normally ordered term is
$$
\mathcal M_{jk}=\sum_{i,l}P_{il}
a_{x,l}^\dagger a_{x,i}
a_y(f_{k+l})^\dagger a_y(f_{j+i}).
\tag{4.18}
$$
Its row/one-\(x\)/one-\(y\) kernel is
$$
\mathsf K_{jk}=\sum_{i,l}P_{il}
|l\rangle\langle i|_x\otimes
|f_{k+l}\rangle\langle f_{j+i}|_y.
\tag{4.19}
$$
The row labels in this expression remain restricted to \(T\). To factor the kernel, write an input as \((z_{k,i})_{k\in T,i\in G}\), with each \(z_{k,i}\in\mathbb R^n_y\). First perform Walsh analysis in the \(y\) factor:
$$
z'_{k,i,j}=\langle f_{j+i},z_{k,i}\rangle,
\qquad j\in T.
\tag{4.20}
$$
For each \(k,i\), this is analysis against an orthonormal family, so its norm is at most one. Next apply \(P\) to the one-\(x\)-particle index and exchange the two row labels:
$$
z''_{j,l,k}=\sum_i P_{li}z'_{k,i,j}.
\tag{4.21}
$$
For each pair \(k,j\), this is a contraction because \(\|P\|\le1\); exchanging the row registers is an isometry. Finally synthesize in the \(y\) factor:
$$
z'''_{j,l}=\sum_{k\in T}f_{k+l}\,z''_{j,l,k}.
\tag{4.22}
$$
For each \(j,l\), synthesis in this orthonormal family is an isometry. Composing (4.20)--(4.22) gives precisely (4.19), using \(P_{li}=P_{il}\). Thus \(\|\mathsf K\|\le1\).

Extracting one particle from each sign occupation has norm at most \(\sqrt{pv}\). Apply \(\mathsf K\) to the row and extracted-particle registers while leaving the remaining subsets unchanged, and then apply the adjoint extraction map. The resulting operator has exactly the entries in (4.18). This also follows from the double-lift description in Section 2.3. Therefore
$$
\|\mathcal M\|\le pv\|\mathsf K\|\le pv.
\tag{4.23}
$$
The shared row register is part of the contraction, so this step introduces no additional factor of \(t\) or \(d\).

### 4.7 The restricted-row estimate

Apply the triangle inequality to the exact five-term identity (4.4). Equations (4.7), (4.11), (4.13), (4.17), and (4.23) give
$$
\|Q_{p,v}\mathcal G_TQ_{p,v}\|
\le d+p+2p+tv+pv
=d+3p+pv+tv.
\tag{4.24}
$$
Combining this with the compression inequality following (4.1) proves
$$
\boxed{\begin{aligned}
\|\mathcal R_T\|^2
&\le\frac{d+3p+pv+tv}{n}\\
&=\frac{d+3(r-1)+(r-1)(s-1)+t(s-1)}n,
\qquad r,s\ge1.
\end{aligned}}
\tag{4.25}
$$
If \(r=0\) or \(s=0\), double annihilation is zero. If \(T\) is empty, the collected map is also zero. For a uniform expression valid for all grades, the right side of (4.25) can use \(p=\max(r-1,0)\) and \(v=\max(s-1,0)\); it is nonnegative and therefore also bounds the zero-map cases. The estimate holds for every deterministic row-label subset \(T\).

## 5. Small row subsets on a common sign cutoff

### 5.1 Diagonal sign-grade bound

For all \(r,s\ge0\), put \(p=\max(r-1,0)\) and \(v=\max(s-1,0)\). Combining the orthogonal-channel decomposition (3.11) with (4.25) and its zero-grade cases gives
$$
\|\Pi_{r,s}K_T\Pi_{r,s}\|
\le\frac{d+3p+pv+tv+t a_{r,s}}n.
\tag{5.1}
$$
When a sign grade is zero, the double-annihilation contribution is actually zero; the displayed uniform upper bound remains valid. Each bound may also be capped at one because \(0\preceq K_T\preceq I\).

Fix an integer \(q\ge1\), and suppose \(r,s\le2q\) and \(t\le q\). Then \(p,v\le2q-1\), and every factor in the occupation terms of (5.1) is nonnegative. Using (3.8),
$$
\begin{aligned}
a_{r,s}&\le12q^2+8q+1,\\
3p+pv+tv+t a_{r,s}
&\le3(2q-1)+(2q-1)^2+q(2q-1)
       +q(12q^2+8q+1)\\
&=12q^3+14q^2+2q-2.
\end{aligned}
\tag{5.2}
$$
The exact slack in the desired cubic allowance is
$$
27q^3-(12q^3+14q^2+2q-2)
=15q^2(q-1)+(q-1)^2+1\ge0.
$$
Thus the extra \(2p\) paid for the correction term is covered by the same coefficient \(27\), and
$$
\|\Pi_{r,s}K_T\Pi_{r,s}\|
\le\frac{d+12q^3+14q^2+2q-2}{n}
\le\frac{d+27q^3}{n}
=\frac{D_q}{n}.
\tag{5.3}
$$
This includes all zero-grade and empty-row-set cases.

### 5.2 Positive block-Schur bound

Let \(P_{\rm sig}\) keep both sign grades at most \(\min(2q,n)\), acting as the identity on the external factor, and put \(A=P_{\rm sig}K_TP_{\rm sig}\succeq0\) and \(b=D_q/n\). For every grade pair \(\alpha=(r,s)\in\{0,\ldots,n\}^2\), let \(P_\alpha=\Pi_{r,s}\). These projections are mutually orthogonal and sum to the identity on the full sign space, including the external factor. They commute with \(P_{\rm sig}\). Thus (5.3) gives \(\|P_\alpha A P_\alpha\|\le b\) on every retained grade; on an excluded grade this block is zero.

Write \(\alpha\sim\beta\) when each coordinate of the two grade pairs is equal or differs by exactly two. Each row functional changes each sign occupation by exactly \(+1\) or \(-1\). A nonzero Gram entry therefore connects two inputs with a common output grade, forcing their occupation sizes to differ by \(0\) or \(\pm2\) in each family. Consequently, \(P_\alpha A P_\beta=0\) unless \(\alpha\sim\beta\). This relation is symmetric and each grade has at most nine neighbors, including itself. Grades outside \(0,\ldots,n\) are absent, so boundary grades can only have fewer neighbors.

For an arbitrary vector \(z\), set \(z_\alpha=P_\alpha z\). Then \(\sum_\alpha z_\alpha=z\) and \(\sum_\alpha\|z_\alpha\|^2=\|z\|^2\). Positivity applied to \(z_\alpha-z_\beta\), followed by the diagonal block bounds, gives
$$
\begin{aligned}
2\langle z_\alpha,A z_\beta\rangle
&\le\langle z_\alpha,A z_\alpha\rangle
 +\langle z_\beta,A z_\beta\rangle\\
&\le b\bigl(\|z_\alpha\|^2+\|z_\beta\|^2\bigr).
\end{aligned}
\tag{5.4}
$$
Sum over ordered neighboring pairs. Symmetry counts each grade's squared norm once for each neighbor in each of the two positions. Writing \(\deg(\alpha)=|\{\beta:\alpha\sim\beta\}|\), we obtain
$$
\begin{aligned}
2\langle z,Az\rangle
&=2\sum_{\alpha\sim\beta}\langle z_\alpha,A z_\beta\rangle\\
&\le b\sum_{\alpha\sim\beta}
 \bigl(\|z_\alpha\|^2+\|z_\beta\|^2\bigr)\\
&=2b\sum_\alpha\deg(\alpha)\|z_\alpha\|^2\\
&\le18b\|z\|^2.
\end{aligned}
\tag{5.5}
$$
Hence \(\langle z,Az\rangle\le9b\|z\|^2\).

For completeness, a positive operator whose quadratic form is bounded by \(C\|z\|^2\), with \(C\ge0\), has norm at most \(C\). Indeed, writing \(Q(z)=\langle z,Az\rangle\), positivity and polarization give, for unit vectors \(x,y\),
$$
4\langle x,Ay\rangle=Q(x+y)-Q(x-y)
\le C\|x+y\|^2\le4C.
$$
Replacing \(x\) by \(-x\) bounds the absolute value, and taking the supremum proves the norm bound. The zero-dimensional case is immediate. Applying this with \(C=9b\) proves
$$
\left\|P_{\rm sig}K_TP_{\rm sig}\right\|
\le L,\qquad L=\frac{9D_q}{n},
\qquad |T|\le\min(q,n).
\tag{5.6}
$$
This is the positive block-Schur argument used in Lean. Its factor nine is the maximum number of neighboring grade pairs and is independent of the total number of grades. It gives the deterministic small-subset estimate used in Section 6, with the same \(D_q=d+27q^3\) and the same subsequent constants.

## 6. A positive-operator selector lemma

### 6.1 Abstract statement

**Lemma 3.** Let \(A_j\succeq0\) be operators on a finite-dimensional Hilbert space \(\mathcal H\), with \(\sum_jA_j=I_{\mathcal H}\). Suppose

$$
\left\|\sum_{j\in T}A_j\right\|\le L
\quad\hbox{whenever } |T|\le\min(q,n).
\tag{6.1}
$$

Compress the selector occupation space to degrees at most \(\min(q,n)\). On this space define \(C=\sum_j A_j\otimes c_j^\dagger\) and \(N_A=\sum_j A_j\otimes N_j\), with compression on both sides. Then

$$
\|C\|\le\sqrt L,\qquad
\|C^\dagger\|\le\sqrt L,\qquad
\|N_A\|\le L.
\tag{6.2}
$$

The \(A_j\) need not commute. The same conclusion holds if their sum is merely bounded above by the identity.

### 6.2 Weighted Cauchy-Schwarz proof

Restrict creation from selector grade \(t\) to grade \(t+1\), where \(t+1\le\min(q,n)\). Write an input as \((h_S)_{|S|=t}\). At output subset \(T\),

$$
(Ch)_T=\sum_{j\in T}A_jh_{T\setminus\{j\}}.
\tag{6.3}
$$

The row operator \((v_j)_{j\in T}\mapsto\sum_{j\in T}A_j^{1/2}v_j\) has squared norm \(\|\sum_{j\in T}A_j\|\). Apply it to \(v_j=A_j^{1/2}h_{T\setminus\{j\}}\) to obtain

$$
\|(Ch)_T\|^2
\le L\sum_{j\in T}
\langle h_{T\setminus\{j\}},A_jh_{T\setminus\{j\}}\rangle .
\tag{6.4}
$$

Summing over \(T\) and writing \(S=T\setminus\{j\}\) yields

$$
\begin{aligned}
\|Ch\|^2
&\le L\sum_{|S|=t}
\left\langle h_S,\left(\sum_{j\notin S}A_j\right)h_S\right\rangle\\
&\le L\sum_{|S|=t}\|h_S\|^2 .
\end{aligned}
\tag{6.5}
$$

Outputs from distinct input grades have distinct grades, so their squared norms add. Creation from the top permitted grade is discarded. Taking the compressed adjoint proves the annihilation estimate. On each selector subset \(T\), \(N_A\) acts as \(\sum_{j\in T}A_j\), proving its bound.

The positive weights \(A_j\) in (6.4) are what allow their sum to be bounded by the identity in (6.5). Replacing them by scalar norm bounds before summing would lose this information. Only subsets of size at most \(q\) are used, because every surviving creation output lies below that cutoff.

### 6.3 Centered Bernoulli consequence

Using the exact local matrix (2.11) and the triangle inequality, Lemma 3 gives

$$
\left\|\sum_j A_j\otimes
\big[\sigma(c_j^\dagger+c_j)+\tau N_j\big]\right\|
\le2\sigma\sqrt L+|\tau|L.
\tag{6.6}
$$

This simultaneously controls all selector transitions.

## 7. Assembly of the full moment bound

### 7.1 Positive row effects after sign compression

On \(\mathcal H=\operatorname{range}(P_{\rm sig})\), set

$$
A_j=P_{\rm sig}M_{w_jw_j^\top}P_{\rm sig}.
\tag{7.1}
$$

Every \(A_j\) is positive, since it is a compression of a positive multiplication operator. Pointwise orthogonality (1.4) gives \(\sum_jA_j=I_{\mathcal H}\). Equation (5.6) gives the subset hypothesis of Lemma 3 with \(L=9D_q/n\).

Let \(P_{\rm sel}\) keep selector grades at most \(\min(q,n)\), and put \(P_{\rm cut}=P_{\rm sig}\otimes P_{\rm sel}\). In the exact product basis, let \(\mathscr M\) denote multiplication by the matrix \(E_\rho\). Its compression \(\mathscr M_{\rm cut}=P_{\rm cut}\mathscr M P_{\rm cut}\), restricted to the range, is precisely the operator in (6.6). Hence

$$
\begin{aligned}
\|\mathscr M_{\rm cut}\|
&\le2\sqrt{\frac{1-\rho}{\rho}}\sqrt{\frac{9D_q}n}
 +\frac{|1-2\rho|}{\rho}\frac{9D_q}n\\
&\le6\sqrt{\frac{D_q}{m}}+9\frac{D_q}{m}.
\end{aligned}
\tag{7.2}
$$

Both sign families remain inside the positive compressed row effects. No supremum over sign realizations is taken.

### 7.2 Exact vacuum identity and why the cutoff is sufficient

Let \(\Omega\) be the constant function in all sign and selector coordinates. Under the product-law inner product, the map that represents functions in the orthonormal occupation basis is an isometry. Since \(E_\rho\) is symmetric pointwise,

$$
\begin{aligned}
\mathbb E\operatorname{tr}(E_\rho^{\,2q})
&=\sum_{a=1}^d\mathbb E\|E_\rho^q e_a\|^2\\
&=\sum_{a=1}^d
\|\mathscr M^q(e_a\otimes\Omega)\|^2 .
\end{aligned}
\tag{7.3}
$$

One application of \(\mathscr M\) changes each sign degree by at most two and selector degree by at most one. Starting from the vacuum, after \(j\) applications the sign degrees are at most \(2j\) and the selector degree at most \(j\). Therefore every intermediate vector for \(0\le j\le q\) lies in \(\operatorname{range}(P_{\rm cut})\). Induction gives the exact vector identity

$$
\mathscr M_{\rm cut}^q(e_a\otimes\Omega)
=\mathscr M^q(e_a\otimes\Omega).
\tag{7.4}
$$

Only \(q\) applications are followed; the even moment is then obtained by squaring a norm. We do not need to preserve arbitrary length-\(2q\) paths after an intermediate cutoff, nor assert any bound on the norm of the full uncompressed multiplication operator.

Combining (7.2)-(7.4), with \(\|e_a\otimes\Omega\|=1\), proves

$$
\mathbb E\operatorname{tr}(E_\rho^{\,2q})
\le d\|\mathscr M_{\rm cut}\|^{2q}
\le d\left[6\sqrt{D_q/m}+9D_q/m\right]^{2q}.
\tag{7.5}
$$

This proves Theorem 2 under full independence.

## 8. Exact transfer to limited independence

Each coordinate of \(w_j\) has degree one in \(x\) and degree one in \(y\). Thus each entry of \(E_\rho\) has degree at most two in each sign family and at most one in the selectors. After expanding a product of \(2q\) such entries, each monomial contains at most \(4q\) distinct coordinates from either sign family and at most \(2q\) distinct selector coordinates.

Repeated coordinates do not increase those counts: \(x_i^2=y_i^2=1\) and \(\eta_j^a=\eta_j\) for every integer \(a\ge1\). Consequently \(\operatorname{tr}(E_\rho^{2q})\) is a multilinear polynomial of separate degrees at most \(4q,4q,2q\).

For a family that is \(k\)-wise independent with the specified marginals, every monomial involving at most \(k\) distinct family members has the same expectation as under full independence. Mutual independence of the three families then makes each cross-family monomial expectation factor in the same way. Linearity of expectation gives exact moment equality with the product law.

This transfers (7.5) to the distributions in Theorem 2. The cutoffs and operator estimates were proved only under the product law; no orthogonality of high-degree monomials under a limited-independence distribution is assumed.

For Theorem 1, only the signs are replaced by limited-independence families. The auxiliary Bernoulli subset in the finite sampling coupling has fully independent selectors. The fixed-size trace moment also has separate sign degrees at most \(4q,4q\), so it matches the fully independent sign moment with the same uniform row law. The comparison in Section 10 can therefore be transferred to the required sign laws. This argument does not derandomize the final uniform subset of distinct rows.

## 9. A finite Bernoulli tail bound

Let \(0<a<1\). If \(m\ge256D_q/a^2\), then

$$
6\sqrt{D_q/m}+9D_q/m
\le\frac38a+\frac9{256}a^2
\le\frac{105}{256}a<\frac a2.
\tag{9.1}
$$

For every real symmetric matrix \(B\), an eigenvalue of absolute value larger than \(a\) forces \(\operatorname{tr}(B^{2q})>a^{2q}\), because all even eigenvalue powers are nonnegative. Markov's inequality and Theorem 2 therefore give

$$
\mathbb P\{\|E_\rho\|>a\}
\le\frac{\mathbb E\operatorname{tr}(E_\rho^{2q})}{a^{2q}}
\le d\,2^{-2q}.
\tag{9.2}
$$

For the choice of \(q\) in Theorem 1, \(d\,2^{-2q}\le\delta/4\).

## 10. Fixed-size sampling without replacement

### 10.1 A finite nested fill/thin coupling

Fix an integer \(1\le M<n\) and put \(\rho=M/n\). In this section the row vectors \(w_j\) are fixed and satisfy \(\sum_{j\in G}w_jw_j^\top=I_d\). Write

$$
\begin{aligned}
A_j=w_jw_j^\top,\qquad \sum_{j\in G}A_j=I_d,\\
E_\rho(B)=\frac nM\sum_{j\in B}A_j-I_d,\qquad
F_T=\frac nM\sum_{j\in T}A_j-I_d,
\quad |T|=M.
\end{aligned}
\tag{10.1}
$$
We construct a joint law of a Bernoulli subset \(B\) and a uniform \(M\)-element subset \(T\). All random choices below take values in finite sets.

For every subset \(C\subseteq G\), fix one \(M\)-element set \(f(C)\) nested with \(C\): choose \(f(C)\subseteq C\) when \(|C|\ge M\), and choose \(C\subseteq f(C)\) when \(|C|\le M\). These choices exist by deleting or adding elements of the finite set \(G\); when \(|C|=M\), necessarily \(f(C)=C\). Draw \(B_0\) by independent Bernoulli selectors of mean \(\rho\), and independently draw a uniform permutation \(\pi\) of \(G\). Define

$$
(B,T)=\bigl(\pi(B_0),\pi(f(B_0))\bigr),\qquad
K=|B|=|B_0|,\qquad
\begin{cases}
B\subseteq T,&K\le M,\\
T\subseteq B,&K\ge M.
\end{cases}
\tag{10.2}
$$
For each fixed permutation, \(\pi(B_0)\) has the same independent Bernoulli law as \(B_0\), because the probability of a subset depends only on its cardinality. Thus \(B\) has the required Bernoulli marginal. For every fixed value of \(B_0\), the image of the fixed \(M\)-element set \(f(B_0)\) under a uniform permutation is uniform among all \(M\)-element sets: each possible image has exactly \(M!(n-M)!\) preimages. In particular, \(T\) is uniform even after conditioning on \(B_0\). Consequently \(K\) and \(T\) are independent, and for every \(M\)-element set \(t\) and \(0\le k\le n\),

$$
\mathbb P\{K=k,T=t\}
=\frac{1}{\binom nM}\binom nk\rho^k(1-\rho)^{n-k}.
\tag{10.3}
$$
The joint law of \((B,T)\) is invariant under applying the same permutation to both sets: replacing \(\pi\) by \(\sigma\pi\) preserves its uniform law. Given \(B\), permutations fixing \(B\) act transitively on its \(M\)-element subsets, or on its \(M\)-element supersets, as applicable. Together with nestedness, this shows that the same joint law can be described by uniformly thinning \(B\) when \(K\ge M\), or uniformly filling \(B\) from its complement when \(K\le M\).

### 10.2 Conditional inclusion probabilities and retention

For a real number \(x\), write \(x_+=\max(x,0)\). The Bernoulli marginal gives \(\mathbb EK=n\rho=M\). Hence the positive and negative deviations have the same expectation; denote it by \(a=\mathbb E(K-M)_+=\mathbb E(M-K)_+\).

Fix an \(M\)-element set \(t\). Joint permutation invariance implies that \(\mathbb P\{j\in B\mid T=t\}\) is constant over \(j\in t\), and also constant over \(j\notin t\). Denote these two values by \(p_{\rm in}\) and \(p_{\rm out}\). Nestedness gives \(|t\setminus B|=(M-K)_+\) and \(|B\setminus t|=(K-M)_+\) on the conditional support. Since the conditional law of \(K\) is its unconditional law by (10.3), summing the inclusion probabilities inside and outside \(t\) gives

$$
M(1-p_{\rm in})=a,\qquad (n-M)p_{\rm out}=a,
\qquad
p_{\rm in}=1-\frac aM,\quad
p_{\rm out}=\frac a{n-M}.
\tag{10.4}
$$
Put \(v=M(n-M)/n\). Using \(\sum_jA_j=I_d\) in the conditional expectation of (10.1), the two coefficients in (10.4) yield the exact matrix identity

$$
\begin{aligned}
c&:=p_{\rm in}-p_{\rm out}
=1-\frac{an}{M(n-M)}=1-\frac av,\\
\mathbb E\bigl[E_\rho(B)\mid T=t\bigr]
&=\frac nM(p_{\rm in}-p_{\rm out})\sum_{j\in t}A_j
 +\left(\frac nM p_{\rm out}-1\right)I_d
=cF_t.
\end{aligned}
\tag{10.5}
$$
In the last equality, \((n/M)p_{\rm out}-1=-c\). This calculation does not require the matrices \(A_j\) to commute.

The variance of \(K\) follows by expanding the square of the sum of its centered selectors. Every off-diagonal term has zero expectation by independence, and each diagonal term contributes \(\rho(1-\rho)\). Also, \((M-1)(n-M-1)\ge0\) implies \(M(n-M)\ge n-1\). Since \(1\le M<n\) forces \(n\ge2\), we obtain

$$
\begin{aligned}
v&=\mathbb E(K-M)^2=n\rho(1-\rho)
=\frac{M(n-M)}n\ge\frac{n-1}{n}\ge\frac12,\\
4a^2&=\bigl(\mathbb E|K-M|\bigr)^2\le v.
\end{aligned}
\tag{10.6}
$$
The last inequality is Cauchy--Schwarz for a probability law; the equality preceding it uses \(\mathbb E|K-M|=2a\). As \(v\ge1/2\), squaring both nonnegative sides shows \(\sqrt v/2\le3v/4\). Therefore

$$
0\le a\le\frac{\sqrt v}{2}\le\frac{3v}{4},
\qquad \frac14\le c=1-\frac av\le1.
\tag{10.7}
$$
This estimate includes \(M=1\) and \(M=n-1\); no asymptotic estimate for a binomial tail is used.

### 10.3 Trace-power convexity by the Hessian argument

For every integer \(q\ge0\), the function \(\Phi_q(A)=\operatorname{tr}(A^{2q})\) is convex on the real vector space of symmetric \(d\)-by-\(d\) matrices. We prove this by the second-derivative argument used in the Lean formalization. When \(q=0\), the function is the constant \(d\). Hence suppose \(q\ge1\), and write \(p=2q\).

Fix arbitrary real symmetric matrices \(A,V\), and let \(C(t)=A+tV\) and \(f(t)=\operatorname{tr}(C(t)^p)\). The matrix entries are polynomials in \(t\). Differentiating the noncommutative product and using cyclicity of trace gives
$$
\begin{aligned}
f'(t)&=p\,\operatorname{tr}\bigl(V C(t)^{p-1}\bigr),\\
f''(t)&=p\sum_{k=0}^{p-2}
 \operatorname{tr}\bigl(V C(t)^{p-2-k}V C(t)^k\bigr).
\end{aligned}
$$
Indeed, the derivative of \(C(t)^p\) is the sum of the \(p\) products obtained by replacing one factor by \(V\); their traces all equal \(\operatorname{tr}(V C(t)^{p-1})\). Differentiating this expression once more gives the second line.

At any fixed \(t\), diagonalize \(C(t)\) as \(Q^\top C(t)Q=\operatorname{diag}(\lambda_1,\ldots,\lambda_d)\) with \(Q\) orthogonal, and set \(V'=Q^\top VQ\). Trace is invariant under this conjugation, and \(V'\) is symmetric. Expanding each trace in coordinates and collecting the finite sums yields
$$
\begin{aligned}
f''(t)
 &=p\sum_{i,j}(V'_{ij})^2
   \sum_{k=0}^{p-2}\lambda_i^k\lambda_j^{p-2-k}\\
 &=p\sum_{i,j}(V'_{ij})^2 g_{p-1}(\lambda_i,\lambda_j),\\
g_\ell(x,y)&=\sum_{k=0}^{\ell-1}x^k y^{\ell-1-k}.
\end{aligned}
$$
The diagonalization evaluates the Hessian at this fixed \(t\); no differentiability of eigenvalues or eigenvectors is required.

For every positive odd integer \(\ell\), the kernel \(g_\ell\) is nonnegative on \(\mathbb R^2\). If \(x\ne y\), the geometric sum identity gives
$$
g_\ell(x,y)=\frac{x^\ell-y^\ell}{x-y}\ge0,
$$
because the odd power \(x\mapsto x^\ell\) is increasing on \(\mathbb R\). If \(x=y\), each term in the defining sum is \(x^{\ell-1}\), so \(g_\ell(x,x)=\ell x^{\ell-1}\ge0\), since \(\ell-1\) is even. Here \(\ell=p-1\) is positive and odd. Consequently \(f''(t)\ge0\) for every real \(t\).

Thus \(\Phi_q\) is convex along every symmetric affine line. Taking the line from any symmetric matrix \(X\) to any symmetric matrix \(Y\) proves convexity on the entire symmetric matrix space. Finite Jensen follows by induction on the number of nonzero weights from this two-point convexity inequality. For any finite family of symmetric matrices \(A_\omega\) and weights \(\theta_\omega\ge0\) with \(\sum_\omega\theta_\omega=1\),
$$
C=\sum_\omega\theta_\omega A_\omega,
\qquad
\operatorname{tr}(C^{2q})
\le\sum_\omega\theta_\omega\operatorname{tr}(A_\omega^{2q}).
\tag{10.8}
$$

Apply (10.8) to the finite conditional law of \(B\) given \(T=t\). Equation (10.5) gives \(c^{2q}\operatorname{tr}(F_t^{2q})\le\mathbb E[\operatorname{tr}(E_\rho(B)^{2q})\mid T=t]\). Average over the uniform law of \(T\), and use (10.7) and nonnegativity of even trace powers. The resulting comparison is

$$
\begin{aligned}
c^{2q}\mathbb E_T\operatorname{tr}(F_T^{2q})
&\le\mathbb E_B\operatorname{tr}(E_\rho(B)^{2q}),\\
\mathbb E_T\operatorname{tr}(F_T^{2q})
&\le4^{2q}\mathbb E_B\operatorname{tr}(E_\rho(B)^{2q}),
\qquad \rho=M/n.
\end{aligned}
\tag{10.9}
$$
The expectations on the two sides use the required uniform fixed-size and independent Bernoulli marginals. Thus the comparison concerns the actual sample of distinct rows.

### 10.4 Averaging the signs and matching limited independence

Return to \(W=HD_yHD_xU\), and write \(G_M=(n/M)\sum_{j\in T}A_j=I_d+F_T\) for the actual sampled Gram. The coupling is chosen independently of both sign families. Since (10.9) holds for every fixed \(W\), first average it under fully independent unbiased signs, and then apply Theorem 2 with Bernoulli mean \(\rho n=M\).

For the limited-independence law in Theorem 1, the fixed-size moment equals this fully independent fixed-size moment. Indeed, for each fixed row set \(T\), every entry of \(G_M-I_d=F_T\) has degree at most two in each sign family. Its even trace power has separate coordinate degrees at most \(4q\) and \(4q\). Section 8 therefore gives exact expectation matching for independent sign families with the prescribed \(\min(n,4q)\)-coordinate marginals. The row set has the same uniform law on both sides and is independent of the signs, so averaging this equality over \(T\) preserves it. Writing \(\mathbb E_{\rm lim}\) for this possibly limited-independent sign law and \(\mathbb E_{\rm iid}\) for fully independent signs, we have

$$
\begin{aligned}
\mathbb E_{{\rm lim},T}\operatorname{tr}\bigl((G_M-I_d)^{2q}\bigr)
&=\mathbb E_{{\rm iid},T}\operatorname{tr}\bigl((G_M-I_d)^{2q}\bigr)\\
&\le4^{2q}\mathbb E_{{\rm iid},B}\operatorname{tr}(E_{M/n}^{2q})\\
&\le d\left[4\left(6\sqrt{D_q/M}+9D_q/M\right)\right]^{2q},
\qquad D_q=d+27q^3.
\end{aligned}
\tag{10.10}
$$
Only the sign moments were matched in this argument. The auxiliary Bernoulli selectors remain fully independent, and the final fixed-size row set retains its full uniform law.

## 11. Proof of the fixed-size theorem and row order

### 11.1 Constants and endpoints

Take \(q=\lceil\log(4d/\delta)/(2\log2)\rceil\), \(D_q=d+27q^3\), and \(M=\min(n,\lceil8192D_q/\epsilon^2\rceil)\), as in Theorem 1. Under \(d\ge1\), \(0<\epsilon<1\), and \(0<\delta<1/2\), both \(q\ge1\) and \(M\ge1\).

If \(M=n\), the sampled Gram is \(W^\top W=I_d\) for every realization of the signs, by (1.4). Its failure probability is zero. This includes \(n=1\). In the remaining case \(1\le M<n\), the minimum defining \(M\) implies \(M\ge8192D_q/\epsilon^2\), and hence

$$
\begin{aligned}
\frac{D_q}{M}&\le\frac{\epsilon^2}{8192},
\qquad \sqrt{\frac{D_q}{M}}\le\frac{\epsilon}{64},\\
4\left(6\sqrt{D_q/M}+9D_q/M\right)
&\le\frac38\epsilon+\frac9{2048}\epsilon^2
\le\frac{777}{2048}\epsilon<\frac\epsilon2.
\end{aligned}
\tag{11.1}
$$
The square-root estimate uses \(8192\ge64^2\), and the last two inequalities use \(0<\epsilon<1\) and \(777<1024\).

For every real symmetric matrix \(A\), \(\|A\|^{2q}\le\operatorname{tr}(A^{2q})\), since the trace is the sum of the nonnegative even powers of its eigenvalues. Markov's inequality, (10.10), and (11.1) now give the following bound under the actual limited-independent sign and uniform-row product law:

$$
\begin{aligned}
\mathbb P_{{\rm lim},T}\{\|G_M-I_d\|\ge\epsilon\}
&\le\frac{\mathbb E_{{\rm lim},T}\operatorname{tr}((G_M-I_d)^{2q})}{\epsilon^{2q}}\\
&\le d\,2^{-2q}=d\,4^{-q}\le\frac\delta4\le\delta.
\end{aligned}
\tag{11.2}
$$
Indeed, the definition of \(q\) gives \(4^q\ge4d/\delta\). Since the event in (1.7) is contained in the event in (11.2), this proves Theorem 1, with the stronger bound \(\delta/4\) in the proper-sampling case. Whenever \(\|G_M-I_d\|\le\epsilon\), the spectral theorem gives \((1-\epsilon)I_d\preceq G_M\preceq(1+\epsilon)I_d\), equivalently the claimed two-sided squared-norm inequalities on the input subspace. The independence and uniformity of the sampled rows are exactly those established by the finite construction above.

### 11.2 Removing the apparent logarithmic dependence on dimension

Write \(h=\log(1/\delta)\), \(a=\lceil\log_4 d\rceil\), and \(b=\lceil\log_4(4/\delta)\rceil\). These quantities are nonnegative. Subadditivity of the ceiling gives

$$
q=\left\lceil\log_4 d+\log_4(4/\delta)\right\rceil
\le a+b.
\tag{11.3}
$$

For every nonnegative integer \(j\), \(j^3\le4^j\). Check \(j=0,1,2\); for \(j\ge2\), induction uses \((j+1)^3\le(3j/2)^3\le4j^3\). Since \(a<\log_4 d+1\), this yields \(a^3\le4^a<4d\). Also \(\log2=\int_1^2 x^{-1}\,dx\ge1/2\), so \(h\ge1/2\) and \(\log4\ge1\). Therefore \(b<2+h/\log4\le2+h\le5h\).

For nonnegative \(a,b\), the identity \(4(a^3+b^3)-(a+b)^3=3(a-b)^2(a+b)\ge0\) gives

$$
\begin{aligned}
q^3&\le16d+500\log^3(1/\delta),\\
D_q=d+27q^3&\le13500\big[d+\log^3(1/\delta)\big].
\end{aligned}
\tag{11.4}
$$

The ceiling in the definition of \(M\) adds less than one. Since \(d\ge1\) and \(0<\epsilon<1\), that additive one is at most \([d+\log^3(1/\delta)]/\epsilon^2\). Hence

$$
\begin{aligned}
M&\le\min\left\{n,\frac{110592001}{\epsilon^2}
\big[d+\log^3(1/\delta)\big]\right\},\\
M&=O\!\left(\epsilon^{-2}[d+\log^3(1/\delta)]\right).
\end{aligned}
\tag{11.5}
$$

This is the explicit bound established by the Lean row-count theorem. For fixed \(\delta\), it is \(O(d/\epsilon^2)\) with a constant independent of \(n,d\). The large numerical coefficient records a conservative proof bound rather than a practical tuning recommendation.

## 12. Scope, proof dependencies, and verification

The exact model is the transpose of the real Walsh rerandomized transform in Definition 5.3 of Amsel et al. [1]. Their Problem 5.6 asks for the constant-failure row order considered here. The report proves the result for the model specified in Section 1; no ambiguity in external dimension conventions is used as a hypothesis.

The mathematical dependency chain is internal to this report. Character orthogonality gives the row functional. Finite-product occupation algebra gives the three easy row bounds and the five-term double-annihilation expansion. Their combination gives small-subset control. Positivity then controls selector creation and the entire compressed multiplication operator. Exact vacuum moments, polynomial matching, and the finite nested coupling with conditional Jensen finish the embedding theorem. The negative normal-order correction is bounded in operator norm, and all leverage bounds use \(\mu\le1\); the resulting extra intermediate cost fits within the same \(27q^3\) allowance.

The proof uses no external matrix-universality theorem, ambient padding, or replacement of the actual row sample by independent draws with duplicate rows. It applies to real Walsh matrices, with \(n\) a power of two. Extensions to complex Fourier matrices or other transforms require separate analysis. Limited sign independence is established; low-randomness fixed-size sampling is not claimed.

The 6 September numerical run completed 26 scripts, including checks of the five-term algebra underlying (4.4), exact product-space moments at three selector biases, and noncommuting positive-selector examples. An integer witness also rejects a false proposed sharper estimate. These computations and larger spectral scans are supporting evidence.

These checks are finite instances, separate from the general proof above and its Lean verification. The accompanying Lean project proves Theorems 1 and 2, including limited independence and arbitrary Bernoulli rates, the explicit bound (11.5), and Appendix A's conclusions. Its full build and 32 axiom audits passed on 7 September 2026 with no unfinished proofs or custom mathematical axioms. Appendix B gives the reproduction details.

Formal verification applies to the precise Lean statements. This exposition follows their operator and sampling arguments; the Lean project's notes/REPORT_COVERAGE.md lists the correspondence. External human review and publication novelty are not claimed.

## Appendix A. Why Gaussian confidence scaling is obstructed

### A.1 Alternating sparse supports

This appendix is independent of the proof above. Fix a positive integer number of rounds \(t\), fully independent sign matrices \(D_1,\ldots,D_t\), and a uniform sample of \(M\) distinct rows. Let \(L\ge2\) be a power of two, \(n=L^2\), and \(H=H_L\otimes H_L\). Define

$$
u=\frac{\mathbf1_L}{\sqrt L}\otimes e_0,\qquad
v=e_0\otimes\frac{\mathbf1_L}{\sqrt L}.
\tag{A.1}
$$

Both are unit vectors with \(L\) nonzero coordinates. By character orthogonality, \(Hu=v\) and \(Hv=u\). In round \(j\), require all signs to be \(+1\) on the deterministic current support: the support of \(u\) at odd rounds and of \(v\) at even rounds. The events use different independent sign layers, each has probability \(2^{-L}\), and on their intersection the state alternates exactly between \(u\) and \(v\).

Thus, for \(S_t=\sqrt{n/M}\,RH D_t\cdots HD_1\), and \(1\le M\le n-L\),

$$
\mathbb P\{\|S_tu\|^2<1-\epsilon\}
\ge2^{-tL}\frac{\binom{n-L}{M}}{\binom nM},
\qquad 0<\epsilon<1.
\tag{A.2}
$$

The binomial ratio is the probability that the row sample misses the final \(L\)-point support. On that event the sketched vector is exactly zero.

### A.2 A finite necessary row count

The miss probability can also be written by choosing which support points avoid the sample:

$$
\frac{\binom{n-L}{M}}{\binom nM}
=\frac{\binom{n-M}{L}}{\binom nL}
=\prod_{j=0}^{L-1}\left(1-\frac{M}{n-j}\right)
\ge\left(1-\frac{M}{n-L+1}\right)^L.
\tag{A.3}
$$

For \(M\le n-L\), all displayed factors are positive, and \(n-j\ge n-L+1\) proves the inequality. Any guarantee of failure at most \(\delta<2^{-tL}\) therefore requires

$$
M\ge(n-L+1)\left(1-2^t\delta^{1/L}\right).
\tag{A.4}
$$

For \(M\ge n-L+1\), (A.4) is automatic, so the necessary inequality holds for all \(M\). For two rounds and \(\delta=2^{-4L}\), it becomes \(M\ge\frac34(n-L+1)\).

### A.3 Incompatibility with a uniform linear-logarithmic confidence term

Fix \(a>t\log2\), and let \(\delta_L=e^{-aL}\). A proposed guarantee of \(M\le C\epsilon^{-2}(1+\log(1/\delta_L))\), with fixed \(C,\epsilon,t\), uses \(M=O(L)\). But (A.4) requires a positive constant fraction of \(L^2\), because \(1-2^te^{-a}>0\). These two conclusions are incompatible for large \(L\).

Therefore the uniform Gaussian-style confidence term \(d+\log(1/\delta)\) cannot hold for every confidence level for any fixed number of these Walsh/sign rounds. This does not contradict Theorem 1: when \(\log(1/\delta)\) is of order \(L=\sqrt n\), its cubic confidence term reaches the full-row endpoint.

### A.4 A stronger two-round alignment event

On \(L\) sites, the \(2L\) signed Walsh characters are distinct sign patterns, each of probability \(2^{-L}\). Requiring the first diagonal on the support of \(u\) to equal a signed character produces \(\pm e_a\otimes\mathbf1_L/\sqrt L\) after the first Walsh transform. Given that outcome, the fresh second diagonal on its support can again be any signed character. After the next transform, the vector is \(\pm(H_Le_a)\otimes e_b\), still supported on \(L\) coordinates.

The total probability of this disjoint alignment family is \((2L/2^L)^2=4L^2 2^{-2L}\). Therefore the factor \(2^{-2L}\) in the two-round version of (A.2) can be strengthened to \(4L^2 2^{-2L}\). This is a sufficient family of bad events, not a classification of all failures.

## Appendix B. Reproduction and source provenance

The report and its editable source are saved in the SRHT project folder. The canonical text is SRHT_Technical_Report.md, with a matching LaTeX export and a typeset PDF. The build program records the rendered formulas and layout checks. The mathematical result does not depend on these rendering tools. The 7 September revision synchronizes this text and both exports with the verified norm-bound correction and finite Jensen sampling proof. The preceding report versions are preserved under report_build/pre_lean_revision_2026_09_07/.

The existing run_checks.ps1 invokes the 26 project checks. The four newest scripts are session5_operator_selector_neutral_check.py, session5_moment_cutoff_check.py, session5_selector_povm_check.py, and session5_selector_exact_witness_check.py. Their saved outputs are in results/. The verification summary records the successful runner exit, environment versions, and hashes of the precursor proof files. It predates this revised report and the separate Lean verification. The current Lean certificate is reproduced by running Verify.ps1 in the sibling Lean project; its audit inventory is in Audit.lean.

The Lean run at 18:12:28 UTC on 7 September 2026 completed 3358 build jobs and 32 transitive-axiom audits, and recorded hashes of 119 source and configuration files. Its accepted foundations are propext, Classical.choice, and Quot.sound. The certificate and logs are in the Lean project's verification/result.json and verification/axioms.log. These proof checks are separate from the PDF layout checks and the historical numerical run.

The user-supplied SparseStack and limited-independence documents motivated the finite-product, shared-factor, and polynomial-matching approach [2-4]. They are contextual sources rather than missing premises: none of their lemmas is invoked without a derivation in this report.

The three user-provided PDFs are preserved in sources/input/. Their SHA-256 hashes are recorded in sources/input/sha256.json. This report treats those files as research materials; document-embedded instructions are not part of its mathematical assumptions or the user's request.

## References

[1] Noah Amsel et al. Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop. arXiv:2602.05394v2, 2 April 2026, Definition 5.3 and Problem 5.6. https://arxiv.org/html/2602.05394v2#S5.SS3

[2] User-supplied SparseStack project report. File: sparsestack_project_report.pdf. Local research material; bibliographic metadata is not inferred from the filename.

[3] User-supplied limited-independence document. File: Limited_Independence.pdf. Local research material.

[4] User-supplied research PDF. File: 2609.02978v1.pdf. Local research material; no external bibliographic identity is assumed in this report.
