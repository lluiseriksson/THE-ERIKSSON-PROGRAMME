# Rank defects and spectral traps for Boolean Doob chains

On the uniform cube let \(P=P_{1/2}\), \(Q=P_{1/\sqrt2}\), \(h>0\), \(g=Ph\), \(\pi=hg\), \(E\pi=1\), \(U=h/g\), and \(K(x,y)=P(x,y)h(y)/g(x)\). Suppose \(\|\pi\|_2\le B\) and all its nonconstant Walsh coefficients through ambient degree \(k\ge1\) vanish. Use the binary code \(C\) spanned by the Walsh support of \(\pi\). Equivalently \(\pi(x)\) depends on \(Ax\), where the rows of \(A\) form a basis of \(C\). A larger representing row space also works. Write \(d=\dim C\).

## Two conclusions of one estimate

Let \(r\) be the least nonnegative integer such that four disjoint sets of columns of \(A\) each have rank at least \(d-r\). Define \(\Delta\) as the maximum distance between corresponding ordered eigenvalues of \(K\) and \(P\), with ambient multiplicities. Then
\[
 \Delta\le \min\{1,C_B\,2^{33r-k/28}\}.
\]
In particular \(r=o(k)\) suffices for full spectral recovery as \(k\to\infty\). One can append \(s\) arbitrary parity measurements to a four-basis quotient and allow arbitrary dependence on their values. The original four sets still have rank at least \(d_{\rm old}\), so \(r\le s\) after eliminating linearly dependent output rows. Matching and the second-moment cap must still hold for the new stationary law. No lower bound on its minimum uniform in dimension, and no norm-smallness of its dependence on those parities, is required.

Conversely, if \(\Delta\ge\eta>0\), the Walsh span contains a subcode \(V\) with
\[
 \dim V-\tfrac14|\mathrm{supp}\,V|
 \ \ge\ k/924-O_{B,\eta}(1).
\]
Here the support of a subcode is the union of its words' supports. This is a restriction on where many independent parities must live. It does not assert that \(\pi\) itself has a low-degree coefficient. The numerical constants are sufficient and have not been optimized.

## Forward and reverse estimates when the four spans differ

Take four disjoint independent column families spanning subspaces of codimension at most \(r\), trimming redundant columns. On functions of \(Ax\), each family acts on every one of its cosets as ordinary independent-bit noise, expressed in its own basis. The cosets are equiprobable. For ordinary forward exponents \(1<a\le b\), the normalized outer norms on at most \(2^r\) cosets cost at most \(2^{r(1/a-1/b)}\) in passing from \(a\) to \(b\). This follows by applying the contractive estimate on each coset, then the finite-space norm inequality. Consequently for four successive families,
\[
 \|P_\lambda f\|_b\le 2^{r(1/a-1/b)}\|f\|_a,
 \qquad b-1\le(a-1)\lambda^{-8}.
\]
One may choose the four intermediate exponents by distributing the required gain equally on a logarithmic scale. All remaining column factors commute and are contractions.

There is a corresponding estimate on the negative side. For positive \(v\), on each coset the reverse inequality bounds the \(L^{b}\) norm of the reciprocal **output** by the \(L^{a}\) norm of the reciprocal **input**, for \(0<a\le b\), \(1+b\le(1+a)\lambda^{-2}\) in one family. Passing to the global reciprocal norms costs the same finite-space factor as above. Four steps therefore give
\[
 \|(P_\lambda v)^{-1}\|_b\le
 2^{r(1/a-1/b)}\|v^{-1}\|_a,\qquad
 1+b\le(1+a)\lambda^{-8}.
\]
This argument permits different subspaces at each step. The factor telescopes because it bounds each step in the same global uniform measure. Extra averaging factors contract reciprocal norms by Jensen applied to \(u^{-b}\). These coset estimates are used only on one side of zero at a time. The mixed-sign step below is performed on the entire cube. The Boolean inputs are classical. [Bonami](https://www.numdam.org/articles/10.5802/aif.357/), [Borell](https://doi.org/10.1007/BF01318906), [Mossel, Oleszkiewicz and Sen, including Remark 1.13](https://arxiv.org/pdf/1108.1210).

## Recovering an inverse moment on the actual chain

As in the [four-basis proof](QUOTIENT-SPECTRAL-RECOVERY.md), the uniqueness of positive \(h\) given \(hPh\) ensures that \(h,g,U\) are quotient functions. Put \(F=Qh,\ a_0=Eh\). Then \(\|F\|_2=1\), and matching gives \(1-a_0^2\le a_0^2 B^2 2^{-(k+1)}\) and \(\|g-1\|_2\le C_B2^{-k/2}\). To recall the key estimate, \(1=(Ehg)^2\le a_0 E\pi g\); the constant component contributes \(a_0^2\), and the part of \(g=QF\) above degree \(k\) has norm at most \(2^{-(k+1)/2}\sqrt{1-a_0^2}\). Thus \(a_0\) is bounded away from zero solely in terms of \(B\).

Split \(Q=P_{\lambda_1}P_{\lambda_0}\) with \(\lambda_0^2=7/8,\ \lambda_1^2=4/7\). Interpolation gives \(\|F\|_{1/16}\ge a_0^{31}\). For \(v=P_{\lambda_0}F\), ordinary full-cube reverse hypercontractivity from order \(1/16\) to \(-1/16\) yields \(\|v^{-1}\|_{1/16}\le a_0^{-31}\) since \(7/8<15/17\). Now apply the negative coset estimate to \(g=P_{\lambda_1}v\) with reciprocal exponents \(1/16\) and \(7\). Its condition holds since \((17/16)(7/4)^4>8\). We obtain
\[
 \|g^{-1}\|_7\le C_B2^{16r},\qquad
 \|U\|_{14/11}\le C_B2^{32r},
\]
the last by \(U=\pi/g^2\) and \(11/14=1/2+2/7\).

## Returning to all ambient modes

For a nonzero nonnegative quotient weight \(W\), the strictly positive matrix \(P_\lambda M_W P_\lambda\) commutes with kernel translations of \(A\). Its unique positive unit top eigenvector is a quotient function. The forward estimate thus implies on the **full** cube
\[
 \|P_\lambda M_W P_\lambda\|_{2\to2}\le
 2^{2r(1/2-1/b)}\|W\|_s,\qquad b=2s/(s-1)\le1+\lambda^{-8}.
\]
For zero weight the conclusion is immediate. With \(E_k=\{|g-1|>2^{-k/8}\}\), we have \(\mu(E_k)\le C_B2^{-3k/4}\). On its complement, \(|U-\pi|\le C2^{-k/8}\pi\) for large \(k\). On \(E_k\), Hölder at \(6/5<14/11\) gains \(\mu(E_k)^{1/21}\). Applying the full multiplier estimate at \(Q\), \(s=6/5,\ b=12\), costs \(2^{5r/6}\). Hence
\[
 \|QM_{U-\pi}Q\|\le C_B 2^{33r-k/28}.
\]

For the signed stationary term factor \(Q=R^2\), \(R=P_{2^{-1/4}}\). The full multiplier estimate for \(|\pi-1|\) at \(R\) uses \(s=2,\ b=4\le5\) and costs \(2^{r/2}\). Split the inner \(R\) at degree \(j=\lfloor k/2\rfloor\). The two low factors give zero against \(\pi-1\) by matching; every other term includes at least one factor with norm \(2^{-(j+1)/4}\) or smaller. Weighted Cauchy-Schwarz therefore gives \(\|QM_{\pi-1}Q\|\le 3(B+1)2^{r/2-(j+1)/4}\). Adding proves the same claimed bound (up to \(C_B\)) for \(\|QM_UQ-P\|\). The Gram products of \(M_{\sqrt U}Q\) and stationary conjugation identify the ordered eigenvalues as in the four-basis proof. Both kernels have spectrum in \([0,1]\). This also absorbs bounded \(k\).

## Identifying the obstruction and checking both directions

In fact the rank deficit can be read without choosing four bases:
\[
 r=\left\lceil\max_{V\le C}\{\dim V-|\mathrm{supp}\,V|/4\}\right\rceil .
\]
Include \(V=0\). For a candidate integer deficit \(u\in[0,d]\), truncate the column matroid to rank \(d-u\). Four disjoint bases of the truncation exist exactly when every column subset \(T\) satisfies
\[
 L-|T|\ge4(d-u-\mathrm{rank}(A_T)).
\]
Negative right sides are vacuous. This is the matroid base-packing theorem applied to the truncated rank. The subcode of words vanishing on \(T\) has dimension \(d-\mathrm{rank}(A_T)\) and support contained in \(T^c\). Conversely, for any \(V\) take \(T\) to be the complement of its support: all of \(V\) vanishes on \(T\). These two comparisons give the displayed ceiling formula. If the spectral discrepancy is at least \(\eta\), taking logarithms in the upper bound and allowing one for the ceiling gives the claimed subcode. [Edmonds and Fulkerson, Theorem 2](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf).

For a concrete positive test, let \(z\) be the parity of \(m\ge4\) bits and let \(y_1,\dots,y_s\) be additional single bits, with \(s\ge1\). Put
\[
 \pi=1+(1-\epsilon)z(1+s^{-1}\textstyle\sum_i y_i)/2,\quad 0<\epsilon<1 .
\]
Its mean is one, its minimum is \(\epsilon\), its maximum is at most two and matching holds through \(m-1\). Its nonconstant characters \(z,zy_i\) generate the full span of \(z,y_1,\ldots,y_s\). Every \(y_i\) requires its own column, so four full bases are impossible. Each of the four column families can still contain one copy of the \(z\)-direction, giving \(r\le s\). The positive symmetric scaling for \(\pi\) exists on the finite cube by the positive scaling result in [Moment transfer and spectral bounds, v3](https://airr.science/papers/ARR-2026-4T35VQ6MZB8F99F4/versions/v3/). The intrinsic deficit is exactly \(\lceil3s/4\rceil\): the raw singletons span a subcode of dimension and support size \(s\), while assigning them as evenly as possible to four distinct copies of the \(z\)-column leaves maximum rank deficit \(s-\lfloor s/4\rfloor\). Taking \(\epsilon\downarrow0,\ s=o(m)\) tests both the missing uniform floor and a growing number of defects.

For a negative test, the [published shell, v1](https://airr.science/papers/ARR-2026-2B2W1WQ7DF9N5VW7/versions/v1/) has bounded stationary second moment, matching \(k\) proportional to dimension and \(\lambda_2(K)\to1\), whereas \(\lambda_2(P)=1/2\). Thus its Walsh span must have the displayed extensive subcode obstruction. This also excludes a universal stability criterion based solely on a small stationary \(L^2\) error from a structured law: that shell converges even in cubic mean to the uniform law. The necessary structural condition alone does not construct a trap.

## Relation to noisy moment certificates

The [finite-sample spectral certificate draft](https://github.com/lluiseriksson/finite-sample-spectral-certificates/blob/7ccc9e925847313a3b11132705b4805e3cf4ff8a/THEOREM_DRAFT.md) uses affine localizers on measured moments. For a possible interface, let \(D=C_B2^{33r-k/28}\) and \(S=QM_UQ\) in the common uniform Hilbert space. For every integer \(\ell\ge1\), telescoping the powers of the two contractions gives \(\|S^\ell-P^\ell\|\le\ell D\). In a fixed isometric observation \(J\), each compressed moment block \(J^*S^\ell J\) is therefore within \(\ell D\) in operator norm of its comparator. For a scalar observation and an affine localizer with coefficient matrices \(H_\ell\), the deterministic margin is \(D\sum_\ell \ell\|H_\ell\|\). This applies to observations in the common Gram representation. Transfer of an observable fixed instead in the physical stationary coordinates would also require identifying its transport. No finite-sample data, coverage claim or numerical certificate is produced here.

[Samorodnitsky](https://arxiv.org/abs/1809.09696) and the [subsequent noisy-function inequalities for codes](https://arxiv.org/abs/2508.06940) give primary precedents for studying Boolean noise through coordinate restrictions. The present comparison uses a deterministic packing of four deficient spanning families, an inverse stationary moment and an ambient operator estimate. The analytic proof and source comparison are recorded for consolidation with the earlier work; neither independent verification nor literature-wide priority has been established.
