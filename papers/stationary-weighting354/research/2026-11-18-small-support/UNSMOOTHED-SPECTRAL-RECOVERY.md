# Spectral recovery above an explicit stationary moment at half noise

This is the complementary upper regime to the metastable shell construction. Work at \(\rho=1/2\). Use uniform probability and the notation \(g=Ph,\pi=hg,U=h/g\), with \(E\pi=1\). Assume a fixed floor \(\pi\ge b>0\), a uniform stationary bound \(\|\pi\|_p\le B\), and vanishing Walsh coefficients through degree \(k\), excluding the constant. Define
\[
 p_*=(17+4\sqrt{13})/9.
\]
**Claim.** For every \(p>p_*\), the ordered spectrum of the actual Doob kernel differs from that of Boolean noise by at most \(C e^{-ck}\) in maximum absolute error, with constants depending only on \(p,B,b\). In particular \(p=7/2\) suffices without smoothing the stationary density. The number \(p_*\) is a sufficient threshold from this proof. Its necessity, and the case of equality, remain open.

## Improvement of the inverse moment

Write \(Q=P_{\sqrt{1/2}}\). Since \(\|Qh\|_2=1\), the floor and Jensen give \(1/g\le Pg/b\) and \(\|1/g\|_9\le1/b\) by applying ordinary hypercontractivity to \(Pg=P_{(1/2)^{3/2}}Qh\). If \(\|1/g\|_q\) is uniformly bounded, \(h=\pi/g\) is bounded in \(L^u\), \(u=pq/(p+q)\). Ordinary hypercontractivity gives \(g\) bounded in \(L^v,\ v=1+4(u-1)\); hence \(1/h\le g/b\) is bounded in the same space. Reverse hypercontractivity gives
\[
 \|1/g\|_{F_p(q)}\le \|1/h\|_v,\qquad F_p(q)=4(1+v)-1=16pq/(p+q)-9 .
\]
Indeed in generalized-mean notation the exponents are \(-F_p(q)<-v<0\); the admissible noise condition is \(\rho^2=(1+v)/(1+F_p(q))\). This uses both forward and reverse inequalities on each iterate, gaining six inverse-moment orders over the elementary half-noise update \(16u-15\). All iterates used below have \(u>1\).

It suffices to take \(p\le7/2\) by norm monotonicity. To get \(\|U\|_t\) bounded for some \(t>3\) via \(U=\pi/g^2\), it suffices to cross \(q_c=6p/(p-3)\). At \(9\), \(F_p(9)>9\) in the asserted range. At \(q_c\) the sign of \(F_p(q_c)-q_c\) is the sign of \(9p^2-34p+9\) (the difference is \(9(9p^2-34p+9)/((p+3)(p-3))\)). Thus the difference is strictly positive at both ends of \([9,q_c]\). It is concave and continuous, so uniformly positive there. Iteration crosses the target strictly in finitely many steps, with bounds independent of \(k,L\). Choose \(t>3\) with \(1/t=1/p+2/q\) at the crossing. As a check at \(p=7/2\), the guaranteed inverse exponents can be decreased successively to \(31,41,85/2\) starting at 9; here \(q_c=42\).

## Matching and the actual spectral sandwich

Put \(a=Eh\) and \(V=1-a^2=\|Qh-a\|_2^2\). Since \(p'<2\), the part of \(g=Q(Qh)\) above degree \(k\) has \(p'\)-norm at most \(2^{-(k+1)/2}\sqrt V\). Matching gives \(E\pi g\le a+B\,2^{-(k+1)/2}\sqrt V\). Cauchy–Schwarz with measure \(h\,d\mu\) gives \(1=(Ehg)^2\le aE\pi g\). It follows that \(\sqrt V\le aB\,2^{-(k+1)/2}\), with \(V=0\) included, and \(\|g-1\|_2\le \sqrt V+1-a=O(2^{-k/2})\).

On the good set \(|g-1|\le 2^{-k/8}\) one has \(|U-\pi|\le C2^{-k/8}\pi\) for large \(k\). The exceptional set has probability \(O(2^{-3k/4})\) by Chebyshev. Both \(U,\pi\) have bounded \(t\)-norm with \(t>3\). Hölder on the exceptional set implies \(\|U-\pi\|_3=O(e^{-ck})\). The finitely many small orders can be absorbed into the prefactor. In particular \(\|QM_{U-\pi}Q\|_{2\to2}\le\|U-\pi\|_3\), since \(\|Q\|_{2\to3}\le1\).

For \(m=\lfloor k/2\rfloor\) split \(Q\) into its Walsh degrees up to \(m\) and above \(m\). Two low factors against the multiplier \(\pi-1\) have zero inner product since the product of the low factors has degree at most \(k\). With \(t'=t/(t-1)\), put \(\theta=\sqrt{(2t'-1)/2}<1\). Factor \(Q=P_{1/\sqrt{2t'-1}}P_\theta\); the first factor contracts \(L^2\) to \(L^{2t'}\). The low part of \(Q\) has \(2\)-to-\(2t'\) norm at most one, and the high part at most \(\theta^{m+1}\). Hölder in the remaining three terms gives \(\|QM_{\pi-1}Q\|\le3(B+1)\theta^{m+1}\).

The actual kernel is reversibly similar to \(M_{\sqrt U}P M_{\sqrt U}\), which has the same ordered spectrum as \(QM_U Q\) by the two Gram products of \(M_{\sqrt U}Q\). The preceding bounds control \(\|QM_U Q-P\|_{2\to2}\); the eigenvalue assertion follows from min–max. This argument does not assert \(\pi\to1\) in \(L^3\) from matching.

## Scope

The general-correlation trap note gives negative examples with stationary exponents slightly greater than three at half noise. This recovery theorem puts \(7/2\) on the positive side, and bounds the possible transition above by \(p_*\). Earlier work in the programme derived regularity and full spectral comparison after smoothing the stationary law; the unsmoothed multiplier split here avoids needing that density to approach one. Primary inputs include [Mossel, Oleszkiewicz and Sen](https://arxiv.org/abs/1108.1210), [Bonami](https://doi.org/10.5802/aif.357) and [the prior version-specific paper](https://airr.science/papers/ARR-2026-4T35VQ6MZB8F99F4/versions/v3/). This is subsequent unassessed work for integration with the generalized counterexample. The remaining bounded question is whether spectral recovery also holds at \(p=p_*\), where the present iteration can approach the crossing without surpassing it.

