# Spectral recovery from a positive edge moment and a lower marginal bound

We use half-noise \(P=P_{1/2}\) on the uniform binary cube \((\mathbb F_2^L,\mu)\), with \(Q=P_{1/\sqrt2}\). For a positive potential \(h\) normalized by \(E hPh=1\), write \(g=Ph,\ \pi=hg,\ U=h/g\). The stationary pair law is \(J(x,y)=\mu(x)P(x,y)h(x)h(y)\), and the Doob transition is \(K(x,y)=P(x,y)h(y)/g(x)\). Subscript zero denotes the reference chain. Put \(\xi=J/J_0,\ s=\pi/\pi_0\), where \(\pi,\pi_0\) are densities relative to \(\mu\). Norms indexed by \(\pi_0\) use probability \(\pi_0\,d\mu\).

Assume \(\|\pi_0\|_2\le B\), the reference stationary law depends only on a linear quotient \(Ax\), and \(t\) disjoint column families each span a subspace of codimension at most \(r\) in the image of \(A\). Only the tested law must match all uniform marginals through ambient order \(k\). The total dimension and the reference minimum need no bounds.

**Four-family result.** Let \(p>4,\ \beta=p/(p-1)\), and \(d\in(0,\infty]\). Under
\[
 \|\xi\|_{p,J_0}\le M,\qquad \|s^{-1}\|_{d,\pi_0}\le M,\qquad
 \beta(1+1/d)<9/8,
\]
four families suffice for the full ordered spectral discrepancy to satisfy
\[
 \Delta\le \min\{1,C 2^{C' r} e^{-c k}\}.
\]
Here the constants may depend on \(p,d,B,M\). Thus \(r=o(k)\) suffices for recovery. The second condition with \(d=\infty\) means \(\pi\ge M^{-1}\pi_0\). In this case **every positive edge order \(p>9\)** suffices. With \(d=p\), **every \(p>17\)** suffices. The two edge moments of order 18 imply these hypotheses, since \(s=E_{J_0}[\xi\mid X]\) and Jensen bounds \(\|s^{-1}\|_{p,\pi_0}\) by \(\|\xi^{-1}\|_{p,J_0}\). The proof itself requires only a reciprocal *vertex* moment.

**Additional families.** For \(\beta(1+1/d)<4/3\), the same conclusion holds with sufficiently many disjoint families \(t=t(p,d)\), independent of \(L,k,r\). Thus any \(p>4\) suffices with a relative stationary floor; any \(p>7\) suffices with \(d=p\). These are sufficient thresholds, not optimality assertions.

## Reference estimate for ambient vectors

Write \(a=Eh_0,\ F=Qh_0\). Then \(\|F\|_2=1\). Cauchy-Schwarz under \(h_0d\mu\) gives \(1\le aE\pi_0g_0\le aB\), as \(\|g_0\|_2\le1\). Interpolation therefore gives \(\|F\|_{1/64}\ge a^{127}\ge B^{-127}\). Factor \(Q=P_{\ell_1}P_{\ell_0}\) with \(\ell_0^2=31/32,\ \ell_1^2=16/31\). The full cube reverse inequality from \(1/64\) to \(-1/64\) applies since \(31/32<63/65\). Then the reverse inequality on the \(t\) column families gives
\[
 \|g_0^{-1}\|_v\le B^{127}2^{64r}\quad
 \text{if }v\ge1/64,\quad 1+v\le(65/64)(31/16)^t .
\]
In each family the noise is standard in a basis on each coset (discard extra columns first, and apply the remaining averages at the end). Comparing the reciprocal norms across at most \(2^r\) cosets incurs \(2^{r(1/a_1-1/a_2)}\) in going between reciprocal exponents \(a_1,a_2>0\). The losses telescope. This uses the [rank-defect argument](RANK-DEFECT-AND-SPECTRAL-TRAPS.md) and the [sharp reverse Boolean inequality](https://arxiv.org/pdf/1108.1210).

For four families take \(q=8/7,\ v=12\); indeed \((65/64)(31/16)^4>13\). There is a fixed \(\rho_*>1/\sqrt2\), strictly below one, such that for \(R=P_{\rho_*}\) as well as \(Q\), and every ambient \(L^2(\mu)\) unit vector \(x\), we have
\[
 \|\,|Rx|/g_0\|_{2q,\pi_0}+\|Rx\|_{2q,\pi_0}\le C_B2^{C'r}. \tag{1}
\]
To verify this, split \(R=P_\lambda P_\gamma\) with \(\gamma^2=1/(2q-1)\), \(\lambda^2=\rho_*^2(2q-1)\). Ordinary hypercontractivity gives \(\|P_\gamma x\|_{2q}\le1\). Jensen gives \(|Rx|^q\le P_\lambda |P_\gamma x|^q\) with input of \(L^2\) norm at most one. The weight \(W=\pi_0g_0^{-2q}\) has bounded \(L^u\) norm up to \(C_B2^{C'r}\) with \(1/u=1/2+2q/v=29/42\). For the full ambient quadratic form \(P_\lambda M_WP_\lambda\), positivity puts its top eigenvector on the quotient by invariance under all kernel translations. The forward \(t\)-family inequality on that quotient and Hölder give the bound when \(2u/(u-1)<1+\lambda^{-2t}\); the finite-coset loss again has the form \(2^{C'r}\). At \(\rho_*=1/\sqrt2\), the strict inequality reads \(84/13<1+(14/9)^4\). Continuity allows a larger fixed \(\rho_*\). The same argument for \(W=\pi_0\) is easier. These details prove (1); the smoothing and ambient-to-quotient inputs are as in the [four-basis proof](QUOTIENT-SPECTRAL-RECOVERY.md).

For the additional-families claim choose \(1<q<3/2\) with \(\beta(1+1/d)+1/q<2\) and \(q>\beta\). Such a choice exists since \(\beta<4/3\). Set \(v=8q\), \(1/u=3/4\). At \(\rho_*=1/\sqrt2\) we have \(\lambda^2=q-1/2<1\). One can choose fixed \(t\) so that both \(1+v<(65/64)(31/16)^t\) and \(8<1+\lambda^{-2t}\). The same continuity argument proves (1). For the four-family claim, the assumed inequality likewise gives \(q>\beta\) and \(\beta(1+1/d)+1/q<2\).

## Testing the true killed chain on a rare set

For \(D\) in the full cube and a real \(f\) supported on \(D\) with \(\|f\|_{2,\pi}=1\), edge Hölder gives
\[
 |\langle f,K f\rangle_\pi|
 \le M\left(E_{J_0}|f(X)f(Y)|^\beta\right)^{1/\beta}
 = M\|Q(h_0|f|^\beta)\|_2^{2/\beta}.
\]
To bound the last norm, test against any unit \(x\). With
\(e=1-\beta/2-\beta/(2d)-1/(2q)>0\), Hölder gives
\[
 E_{\pi_0}\big[(s |f|^2)^{\beta/2}s^{-\beta/2}|Qx|/g_0\,\mathbf1_D\big]
 \le M^{\beta/2} C_B 2^{C'r}\pi_0(D)^e.
\]
Here \(\pi_0(D)=\int_D\pi_0d\mu\) and the four reciprocal exponents are \(\beta/2,\beta/(2d),1/(2q),e\), with the infinity convention. This bounds the absolute dual pairing since \(h_0=\pi_0/g_0\). It follows that
\[
 \|QM_{U\mathbf1_D}Q\|
 =\|\mathbf1_D K\mathbf1_D\|_{2\to2,\pi}
 \le C 2^{C'r}\,\pi_0(D)^{2e/\beta}. \tag{2}
\]
The equality uses stationary conjugation and the two Gram products of \(M_{\sqrt{U}\mathbf1_D}Q\). Taking the true-chain quadratic form directly is what eliminates the reciprocal edge likelihood. Also \(\|s\|_{p,\pi_0}\le M\) by conditional Jensen. By (1) and \(q>\beta\), \(\|QM_{\pi\mathbf1_D}Q\|\le C2^{C'r}\pi_0(D)^{1/\beta-1/q}\), with strict positive exponent. The same estimate holds with \(R\) in place of \(Q\).

## From matching to all eigenvalues

The derived bound \(\|\pi\|_{8/5}\le C_{B,M}\) follows by Hölder on \(E_{\pi_0}\pi_0^{3/5}s^{8/5}\), using \(E_{\pi_0}\pi_0\le B^2\) and \(\|s\|_{4,\pi_0}\le M\). For the true \(F_1=Qh,\ a_1=Eh,\ V=1-a_1^2\), factor \(Q=P_{\sqrt{3/5}}P_{\sqrt{5/6}}\). The first operator contracts \(L^2\) into \(L^{8/3}\); the second attenuates all ambient degrees above \(k\) by at least the factor \((5/6)^{(k+1)/2}\) in norm. As \(1\le a_1 E\pi g\) and matching annihilates the nonconstant low part, \(V\le C a_1 (5/6)^{(k+1)/2}\sqrt V\). This gives \(\|g-1\|_2\le C(5/6)^{k/2}\). The set \(D=\{|g-1|>(5/6)^{k/8}\}\) has \(\mu(D)\le C(5/6)^{3k/4}\) and \(\pi_0(D)\le B\sqrt{\mu(D)}\).

Use (2) and the corresponding \(\pi\) estimate on \(D\). Off \(D\), \(|U-\pi|\le C (5/6)^{k/8}\pi\) for large \(k\). This bounds \(QM_{U-\pi}Q\) by \(C2^{C'r}e^{-ck}\). For the signed term \(QM_{\pi-1}Q\), split \(Q=R P_\alpha\), \(\alpha=(\sqrt2\rho_*)^{-1}<1\), at degree \(j=\lfloor k/2\rfloor\) in \(P_\alpha\). Its two low factors cancel against \(\pi-1\). Its three remaining terms together have norm at most \(3\|RM_{|\pi-1|}R\|\alpha^{j+1}\). The full-set estimate for \(R\) bounds the multiplier by \(C2^{C'r}\). The ordered eigenvalues follow from Gram conjugation and min-max. Small \(k\) are covered by contraction.

## An explicit distinction from order 84

Use the uniform reference. Take \(n\) disjoint blocks each of length \(m\); let \(A\) mean all parities are positive. Put \(H=2^{n/40}\) on \(A\) and one elsewhere. Then \(Z=E HPH\to1\) since \(1\le Z\le EH^2\to1\). Under the ordinary noise pair law, \(\xi=H(X)H(Y)/Z\) has bounded positive moment norm of order 18 by Cauchy-Schwarz and \(EH^{36}\le 1+2^{-n/10}\). Its reciprocal is bounded by \(Z\). But \(E_{J_0}\xi^{84}\ge Z^{-84}(EH^{84})^2\to\infty\) by positivity of the noise spectrum. Matching through \(m-1\) holds because \(\pi\) depends on full block parities. Taking both \(m,n\to\infty\) verifies strict enlargement of the earlier two-sided moment class at the same reference. A uniform reference is also a quotient law for the block parity map, which supplies four column bases when \(m\ge4\).

## Uniform reference as a boundary check

The positive order \(p>4\) in the many-family criterion is not a necessity theorem. At the uniform reference, with the additional absolute floor \(\pi\ge b>0\), a separate estimate works for every \(p>(15+3\sqrt{13})/8\). Indeed positivity of \(P\) as a quadratic form yields \((Eh^p)^2\le E_{J_0}\xi^p\). Forward hypercontractivity gives \(g\) bounded in \(L^{4p-3}\); \(1/h=g/\pi\le g/b\). Reverse hypercontractivity from order \(-(4p-3)\) to \(-(16p-9)\) gives a uniform \(L^{16p-9}\) bound on \(1/g\). Hence \(U=h/g\) has a bounded moment strictly above three exactly when \(1/p+1/(16p-9)<1/3\) in this sufficient estimate. Also \(\|\pi\|_p\le M\) by conditional Jensen, with \(p>3\). Matching then gives exponential recovery by the exceptional-set \(L^3\) estimate and signed low/high split in the [unsmoothed proof](UNSMOOTHED-SPECTRAL-RECOVERY.md). This calculation is for the uniform reference only. The unrestricted stationary-moment endpoint in the programme remains open.

This analytic supplement extends the [stationary edge note](STATIONARY-EDGE-MOMENT-TRANSFER.md). Neither the noisy-function inputs nor the general theory of likelihood-moment contraction are original here. The conclusions concern deterministic finite-cube operator bounds. No exact-PDF score or independent validation is attributed to this supplement.
