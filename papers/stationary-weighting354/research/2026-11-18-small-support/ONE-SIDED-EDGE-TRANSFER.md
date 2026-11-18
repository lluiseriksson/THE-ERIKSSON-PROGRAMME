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

## Counterexample without lower marginal control

The lower-tail question from this note has a negative answer even when the reference is uniform and positive edge moments of every fixed order converge to their reference values. The same sequence works for all those orders.

**Theorem.** Prescribe any integers \(1\le k_L=o(L)\). There exist strictly positive half-noise Doob chains on all sufficiently large \(L\)-cubes with the following properties. Under the uniform vertex law \(\mu\) and the ordinary stationary noise pair law \(J_0(x,y)=\mu(x)P(x,y)\), writing \(\xi=J/J_0\),
\[
 \widehat\pi(S)=0\quad(1\le |S|\le k_L),\qquad
 \|\xi-1\|_{p,J_0}+\|\pi-1\|_{p,\mu}\longrightarrow0
 \quad\text{for every fixed }1\le p<\infty.
\]
Yet \(\lambda_2(K)\to1\), whereas \(\lambda_2(P)=1/2\). For every fixed \(b>0\), \(E_\mu\pi^{-b}\to\infty\). Exact matching in this assertion is for the vertex marginals. The convergence assertion for consecutive pairs is in the displayed probability norms.

### Choosing translations before defining the potential

Put \(N=\sum_{j=1}^{k_L}\binom Lj\), so \(\log(4N)=o(L)\) by the binary entropy bound. Draw \(\lceil\log_2(2N)\rceil\) independent uniform sign vectors. For a fixed nonconstant character the probability of being one on every draw is \(2^{-\lceil\log_2(2N)\rceil}\). A union bound gives a choice for which the multiplicative subgroup \(G\) generated by the draws has no annihilating character of degree \(1,\ldots,k_L\). Its size is at most \(4N\). This is the elementary random linear-code argument. Exact invariance under \(G\) will enforce matching independently of how small the potential becomes.

Let \(d\) be an attainable sign average closest to \([(\log(4N)+\log(L+1))/L]^{1/8}\). Then \(d\to0\), \(\log|G|+\log L=o(Ld^4)\), and \(Ld^4\to\infty\). Rounding changes the average by at most \(1/L\). For \(c\in G\) put \(m_c(x)=L^{-1}\sum_i c_i x_i\). Define
\[
 T=\bigcup_{c\in G}\{m_c=d\},\qquad E=\bigcup_{c\in G}\{m_c>d^2\},
 \qquad M=\exp(Ld^{5/2}).
\]
Eventually \(T\subset E\). Take \(H=M\) on \(T\), \(H=e^{-L}\) on \(E\setminus T\), and \(H=1\) elsewhere. Set \(Z=E_\mu HPH\) and \(h=H/\sqrt Z\). The sets are invariant under the group, as are \(H,PH,\pi=HPH/Z\). For each forbidden character there is a translation that flips its sign, proving the claimed exact cancellation.

### The forward likelihoods converge together

Hoeffding and the union bound give
\[
 \mu(E)\le |G|e^{-Ld^4/2},\qquad
 \mu(T)\le |G|e^{-Ld^2/2}.
\]
For each fixed \(a\ge1\), \(E_\mu|H-1|^a\le\mu(E)+M^a\mu(T)\to0\), since \(d^{5/2}=o(d^2)\). Under \(J_0\) both one-coordinate-in-time marginals equal \(\mu\). Thus
\[
 \|H(X)H(Y)-1\|_{p,J_0}
 \le \|H-1\|_{2p,\mu}\|H\|_{2p,\mu}+\|H-1\|_{p,\mu}\to0.
\]
In particular \(Z\to1\). This proves convergence of \(\xi=H(X)H(Y)/Z\); conditional expectation given \(X\) gives the vertex assertion. The constants need not be uniform in the moment order.

### Why a starting point on the union stays there

Fix \(x\in T\), and take any \(c\) with \(m_c(x)=d\). The ordinary probability \(q\) of landing back on this individual shell satisfies
\[
 q\ge \exp[-Ld^2/6-O(Ld^4+\log L)] .
\]
For completeness the four stationary joint sign probabilities after centering at \(c\) are \(3/8,1/8,1/8,3/8\), in the order \(++,+-,-+,--\). Use equal integer counts nearest \(L/8\) for the off-diagonals and choose the two remaining counts to give both margins magnetization \(d\). The joint type differs from \((3/8+d/2,1/8,1/8,3/8-d/2)\) by \(O(1/L)\). All entries stay in a fixed compact subset of the positive simplex. The factorial type bound gives joint mass at least \(\exp[-(3L/4)I(4d/3)-O(\log L)]\), where \(I(d)=((1+d)\log(1+d)+(1-d)\log(1-d))/2\). Divide by the upper bound \(e^{-LI(d)}\) for the first shell. Its rows have equal return probability by coordinate permutations. The difference \((3/4)I(4d/3)-I(d)=d^2/6+O(d^4)\) proves the bound uniformly for these shrinking shells.

To land outside \(E\) requires \(m_c(Y)\le d^2\). Conditional on \(x\), the signs \(c_iY_i\) are independent with total mean \(Ld/2\) and variance \(3/4\) each. For each centered sign, its log moment generating function at \(-t\) is \(3t^2/8+O(|t|^3)\) for small \(t\), uniformly in the two possible initial signs. Chernoff at \(t=4(d/2-d^2)/3\) therefore gives
\[
 P_x(E^c)\le \exp[-Ld^2/6+O(Ld^3)] .
\]
Matching the leading \(1/6\) in these two estimates is essential. The numerator for leaving \(T\), weighted by \(H\), is bounded by \(e^{-L}+P_x(E^c)\). The denominator \(PH(x)\) is at least \(Mq\). Since \(Ld^3+\log L=o(Ld^{5/2})\), uniformly for \(x\in T\) the exit probability is at most \(\exp[-Ld^{5/2}/2]\) for all sufficiently large \(L\). Multiple shell membership can only help the denominator. Moreover \(0<\pi(T)\le\|\pi\|_2\sqrt{\mu(T)}\to0\), where \(\pi(T)=\int_T\pi\,d\mu\). Testing the centered indicator of \(T\) in the gap variational formula yields \(1-\lambda_2(K)\le e^{-Ld^{5/2}/2}/(1-\pi(T))\to0\).

### Where the missing lower moments go

One center's shell at the first attainable magnetization strictly above \(d^2\) has uniform mass at least \(\exp[-O(Ld^4+\log L)]\), again by the factorial type bound. It lies in \(E\), and the upper bound on \(\mu(T)\) is of smaller order. Therefore \(\mu(E\setminus T)\ge e^{-O(Ld^4)}\). On this set \(\pi\le e^{-L}M/Z\). For every fixed \(b>0\) this gives \(E_\mu\pi^{-b}\ge Z^b\exp[bL-bLd^{5/2}-O(Ld^4)]\to\infty\).

The example resolves the necessity question in the following sense: forward edge control, even convergence in every finite positive moment, cannot alone guarantee full spectral recovery. It does not determine the optimal reciprocal-moment exponent. It also makes the uniform floor in the earlier stationary-moment problem consequential: the example satisfies the stationary upper bound at the programme endpoint but violates that floor. The problem with the floor remains open. Fixed positive *linear* matching fraction and simultaneous convergence in all finite positive edge moments are outside this construction.

The single-shell joint-type estimate extends the [published AIRR shell](https://airr.science/papers/ARR-2026-2B2W1WQ7DF9N5VW7/versions/v1/) and the [general-correlation calculation](ALL-CORRELATIONS-SHELL-TRAP.md). The group orbit enforces the exact marginals; shrinking magnetization separates the cost of the spike from the cost of returning and retains all finite forward moments. Classical bounded independence and Hamming-sphere noise have primary precedents in [Alon, Babai and Itai](https://web.math.princeton.edu/~nalon/PDFS/Publications2/A%20fast%20and%20simple%20randomized%20parallel%20algorithm%20for%20the%20maximal%20independent%20set%20problem.pdf) and [Polyanskiy](https://arxiv.org/abs/1309.3014). This is an analytic construction; no global priority or formal verification is asserted.

## How much reciprocal growth can matching absorb?

Let \(H_{18}=\|s^{-1}\|_{18,\pi_0}\), and hold the forward edge norm \(\|\xi\|_{18,J_0}\) and the reference bound \(B\) fixed. All logarithms below are natural. Write \(\Delta\) for the maximum ordered eigenvalue difference from ordinary half noise. When \(k\to\infty\), each of the following strict inequalities implies \(\Delta\to0\):
\[
\begin{array}{ll}
\displaystyle\limsup k^{-1}\log H_{18}<\log(6/5)/288
   &\text{for four reference families with }r=o(k),\\[2mm]
\displaystyle\limsup k^{-1}\log H_{18}<11\log(2)/54
   &\text{for the uniform reference.}
\end{array}
\]
In particular bounded reciprocal norm can be replaced by subexponential growth in \(k\). These coefficients are sufficient. The order of growth is sharp in the sense proved below.

**Proof.** In the killed-chain estimate (2), keeping the forward and reciprocal constants separate gives the factor \(\|\xi\|_{18,J_0}H_{18}\): the reciprocal norm first appears to the power \(\beta/2\) and the dual estimate is then raised to \(2/\beta\). All remaining terms in the proof of recovery use only forward moments. For four families take \(D=\{|g-1|>(5/6)^{\eta k}\}\), where \(0<\eta<1/2\). Matching and Chebyshev give \(\pi_0(D)\le C(5/6)^{(1/2-\eta)k}\). At \(\beta=18/17,\ q=8/7,\ d=18\), the spare Hölder exponent is \(1/272\), so \(2e/\beta=1/144\). The killed term is at most \(C2^{C'r}H_{18}(5/6)^{(1/2-\eta)k/144}\). The off-set error and the remaining signed and unsigned terms still vanish exponentially for fixed \(\eta\) and \(r=o(k)\). Strict slack in the claimed rate permits choosing \(\eta>0\) sufficiently small.

For the uniform reference \(h_0=g_0=\pi_0=1\), the ordinary forward inequality gives \(\|Qx\|_3\le1\) for each unit vector. Thus for the killed term \(q=3/2\), \(e=11/102\), and \(2e/\beta=11/54\). Jensen gives \(\|\pi\|_2\le\|\xi\|_{18}\). In the matching estimate for \(V=1-(Eh)^2\), write \(a=Eh,\ F=Qh\). The inequality \(1\le a E\pi g\), matching, and \(\|F-a\|_2=\sqrt V\) give
\[
 V\le a\|\pi-1\|_2\,2^{-(k+1)/2}\sqrt V,
 \qquad \|g-1\|_2\le C2^{-k/2}.
\]
Here \(Q\) acts on the degree tail of \(F\) and \(1-a\le V\). Now use \(D=\{|g-1|>2^{-\eta k}\}\). Its uniform probability is at most \(C2^{-(1-2\eta)k}\). The other multiplier bounds can keep the strictly smaller \(q=8/7\) and the earlier \(R\); the endpoint \(q=3/2\) is needed only for \(Q\) in (2). Letting the strict rate determine \(\eta\) proves the second claim.

### A failure at exponential reciprocal cost and linear matching order

Fix any finite \(p\ge18\). There are constants \(\delta,c,C>0\), depending on \(p\), and positive chains for every sufficiently large \(L\) such that, for \(k=\lfloor\delta L\rfloor\),
\[
 \widehat\pi(S)=0\ (1\le |S|\le k),\qquad
 \|\xi-1\|_{p,J_0}+\|\pi-1\|_{p,\mu}\le Ce^{-cL},\qquad
 1-\lambda_2(K)\le Ce^{-cL},\qquad
 \log\|\pi^{-1}\|_{18,\mu}=\Theta(k).
\]
The reference is uniform. The prescribed forward order is fixed before constructing the family.

Choose \(\epsilon=1/(16p)\) and \(0<\alpha<\epsilon/16\). Choose a sufficiently small fixed \(u>0\), then an attainable \(u_L=u+O(1/L)\). Choose \(0<\gamma<\alpha^2u^2/8\) and \(0<\delta<1/2\) with binary entropy in nats strictly below \(\gamma/2\). The group construction above gives exact matching through \(k\) with \(|G|\le e^{\gamma L}\) for all large \(L\). With the previous notation take shells \(m_c=u_L\), mask \(E=\bigcup_c\{m_c>\alpha u_L\}\), and set the potential equal to \(M=e^{\epsilon L u_L^2}\) on their union \(T\), to \(e^{-Lu_L^2/4}\) on \(E\setminus T\), and to one elsewhere. Normalize as before.

The union bounds now have exponents \(\gamma-\alpha^2u_L^2/2\) and \(\gamma-u_L^2/2\) per coordinate. Since \(2p\epsilon=1/8\), both \(\mu(E)\) and \(M^{2p}\mu(T)\) decay exponentially in \(L\). The product estimate in the preceding construction gives the asserted exponential likelihood bounds and \(Z=1+O(e^{-cL})\). Invariance gives exact matching.

The individual return estimate remains \(q_{\rm ret}\ge\exp[-Lu_L^2/6-O(Lu_L^4+\log L)]\). The conditional Chernoff estimate with threshold \(\alpha u_L\) gives
\[
 P_x(E^c)\le\exp[-(2/3)(1/2-\alpha)^2 L u_L^2+O(Lu_L^3)]\quad(x\in T).
\]
The difference of the leading rate coefficients is \(2\alpha(1-\alpha)/3<\epsilon/8\). The Taylor bounds are uniform for \(u_L\) near zero and \(0<\alpha<1/16\). Choose \(u\) small enough that the combined remainder per \(Lu_L^2\) is below \(\epsilon/4\) for all large \(L\), including the logarithmic term. Both \(P_x(E^c)/(Mq_{\rm ret})\) and \(e^{-Lu_L^2/4}/(Mq_{\rm ret})\) are exponentially small. The centered-indicator test from the preceding section proves the gap bound.

Finally \(H(x),PH(x)\ge e^{-Lu_L^2/4}\) for the unnormalized potential, so \(\|\pi^{-1}\|_\infty\le Ze^{Lu_L^2/2}\). This gives the \(O(k)\) upper bound for its log. For the lower bound, any subsequence with a limiting inferior rate strictly below \(11\log(2)/54\) would have a further subsequence satisfying the uniform recovery theorem, contradicting \(\lambda_2(K)\to1\). Thus \(\liminf k^{-1}\log\|\pi^{-1}\|_{18,\mu}\ge11\log(2)/54\). Determining the best coefficient between the sufficient and counterexample rates remains open.

### Consequence for observing a spectral gap from a stationary trajectory

Even a test that sees every coordinate at every observed time can miss this trap. Write \(\mathcal L_n,\mathcal L^0_n\) for the laws of \(n\) transitions started in each chain's own stationary law. Put \(v=\|J-J_0\|_{\rm TV}\). Marginalization gives \(\|\pi\,d\mu-\mu\|_{\rm TV}\le v\). Also
\[
 \int\|K(x,\cdot)-P(x,\cdot)\|_{\rm TV}\,\pi(x)d\mu(x)
 \le v+\|\pi\,d\mu-\mu\|_{\rm TV}\le 2v.
\]
The first inequality inserts the joint law with initial density \(\pi\) and reference transition \(P\). Replace transitions from the last to the first, leaving a stationary \(K\) prefix at each replacement. Contraction by the common suffix and replacement of the initial law give \(\|\mathcal L_n-\mathcal L^0_n\|_{\rm TV}\le(2n+1)v\). Here \(v\le Ce^{-cL}\); for \(n\le e^{cL/2}\), every test has the sum of its two error probabilities at least \(1-o(1)\). Yet the reference gap is exactly \(1/2\) and the other gap is exponentially small. The witness concerns passive stationary observations; it makes no assertion about chosen initial states or direct access to the transition matrix.

This connects the programme's [AIRR stationary-moment paper](https://airr.science/papers/ARR-2026-4T35VQ6MZB8F99F4/versions/v2/) to the observation question in [finite-sample spectral certificates](https://github.com/lluiseriksson/finite-sample-spectral-certificates/tree/7ccc9e925847313a3b11132705b4805e3cf4ff8a). That repository studies noisy block moments with a specified sampling model and witness-dependent power. The path bound above specifies a different observation experiment and does not transfer a sample bound across models. The [transfer-matrix dictionary](https://github.com/lluiseriksson/lean-transfer-matrix/tree/2b9ad0fdf5aa45e220c87a0f0e84106d6869a007) explicitly requires reconstruction assumptions for its converse from clustering. [Kirshner and Samorodnitsky](https://arxiv.org/abs/1909.11929) give near-extremal noise stability properties of Hamming spheres, and [Polyanskiy](https://arxiv.org/abs/1309.3014) studies norms of spherical averages. Those results concern the reference cube and supply context for the shell geometry. This comparison establishes neither global priority nor independent verification of the present analytic proof.

Single-trajectory lower bounds for estimating the gap of a general reversible chain were established by [Hsu et al.](https://www.cs.columbia.edu/~djhsu/papers/mixingest-aap.pdf). The restriction in this construction is the common half-noise Doob model together with exact linear-order coordinate matching and exponentially close stationary edge laws. With a state space of size 2 to the power L, the displayed observation horizon is exponential in dimension and polynomial in the number of states.


### Adaptive sampling with a hidden translation

Suppose the observer can choose any starting vertex at each step, observe one independent conditional draw from its transition row, and adapt the next choice to all previous replies. Give the observer the reference and the entire list of alternative kernels \(K_z(x,y)=K(xz,yz)\) for \(z\) in the sign cube. Only the active alternative is hidden. Every translate has the same spectrum, moment bounds and matching order. With \(m\) row samples, every randomized test has null error plus worst-case alternative error at least \(1-2mv\).

Indeed, averaging the row discrepancy against the **uniform** law also gives at most \(2v\): insert the joint law with initial density one and transition \(K\) between \(J_0\) and \(J\). Let \(T_P\) and \(T_z\) be the transcript laws. For a fixed \(z\), replace replies from the last to the first. At replacement \(i\) the prefix is generated entirely under \(P\), so its chosen vertex \(X_i\) has a law independent of \(z\). Conditional on this prefix and the observer's random seed, passing the two possible reply laws through the common adaptive suffix contracts total variation. It follows that
\[
 \|T_P-T_z\|_{\rm TV}
 \le\sum_{i=1}^{m}E_P\big[\|P(X_i,\cdot)-K_z(X_i,\cdot)\|_{\rm TV}\big].
\]
For uniform \(z\), translation invariance of \(P\) turns the mean of each summand into the uniform mean row discrepancy, regardless of \(X_i\). Convexity gives \(\|T_P-E_zT_z\|_{\rm TV}\le2mv\). Testing this mixture and bounding average error by worst-case error proves the claim. Thus even adaptive restarts with \(m\le e^{cL/2}\) cannot give uniformly reliable discrimination in this restricted model. The quantifier is worst case over hidden translates for each test. Revealing a trap location or returning exact row probabilities changes the observation experiment.

[Fried and Wolfer](https://proceedings.mlr.press/v151/fried22a/fried22a.pdf) study identity testing from a single trajectory under a transition-distance separation. Here separation is in the spectral gap, and the observer may restart at each query. The proof uses only total variation contraction and translation symmetry after the matched family has been constructed.
