# Stationary edge moments and spectral recovery

Use uniform probability \(\mu\) on the binary cube, half-noise \(P=P_{1/2}\), and \(Q=P_{1/\sqrt2}\). For two positive normalized potentials \(h_i\) define \(g_i=Ph_i,\ \pi_i=h_i g_i,\ U_i=h_i/g_i\). The canonical stationary law of a consecutive pair is
\[
 J_i(x,y)=\mu(x)P(x,y)h_i(x)h_i(y).
\]
Subscript zero denotes the reference; omit the other subscript for the tested law. The reference density on vertices satisfies \(\|\pi_0\|_2\le B\) and factors through a binary quotient of four-family rank deficit \(r\) as in the [rank-defect theorem](RANK-DEFECT-AND-SPECTRAL-TRAPS.md). Assume the tested stationary law matches the uniform marginals through degree \(k\ge1\). All vertex norm subscripts \(\pi_0\) denote probability measure \(\pi_0d\mu\).

**Theorem.** Let \(\xi=dJ/dJ_0\). If
\[
 \max\{\|\xi\|_{84,J_0},\|\xi^{-1}\|_{84,J_0}\}\le M ,
\]
then the error in any corresponding ordered full-cube eigenvalue of the Doob chain and \(P\) is bounded by
\[
 \min\{1,C_{B,M}\,2^{33r}(2/3)^{k/112}\}.
\]
The moments are bounded by a fixed constant, without a requirement that they approach one. Neither density needs a uniform floor. Only the tested law needs matching, and only the reference needs a prescribed second moment. The finite exponent 84 is a sufficient choice.

## From an edge observation to the multiplier

Write \(u=h/h_0,\ s=\pi/\pi_0\) and let \(K_0\) be the reference transition. Then \(\xi(x,y)=u(x)u(y)\), \(s=uK_0u=E_{J_0}[\xi\mid X]\), and \(U/U_0=u/(K_0u)\). Conditional Jensen gives \(\|s\|_{84,\pi_0}\le M\). In addition, \(K_0\) is positive semidefinite in its stationary space, by conjugation to \(M_{\sqrt{U_0}}P M_{\sqrt{U_0}}\), and fixes constants. Hence for \(\alpha=84,-84\),
\[
 (E_{\pi_0}u^\alpha)^2\le
 \langle u^\alpha,K_0u^\alpha\rangle_{\pi_0}=E_{J_0}\xi^\alpha .
\]
Jensen for the convex negative power and stationarity imply \(\|(K_0u)^{-1}\|_{84,\pi_0}\le\|u^{-1}\|_{84,\pi_0}\). Thus \(\|U/U_0\|_{42,\pi_0}\le M\) by Hölder. Finally, integrating \(\pi^{7/4}\) under \(\mu\) amounts to integrating \(\pi_0^{3/4}s^{7/4}\) under \(\pi_0d\mu\). Hölder with \(4/3,4\) and \(E_{\pi_0}\pi_0\le B^2\) give \(\|\pi\|_{7/4}\le C_{B,M}\).

The conditional Jensen step is the usual marginal contraction of likelihood moments. The simultaneous inverse estimate uses positivity of the reference spectrum and the symmetric scaling factorization of the edge law. Background on marginal contraction is given by [van Erven and Harremoës](https://arxiv.org/abs/1206.2459).

## Matching with the derived moment

Put \(F=Qh,\ a=Eh,\ V=1-a^2\). Then \(\|F\|_2=1\), \(\|F-a\|_2=\sqrt V\). In \(g=QF\) split \(Q=P_{\sqrt{3/4}}P_{\sqrt{2/3}}\). The first factor contracts \(L^2\) into \(L^{7/3}\). The second contracts ambient degrees above \(k\) in \(L^2\) by at least the factor \(\theta^{k+1}\), \(\theta=\sqrt{2/3}\), in the sense of an upper norm bound. Therefore matching and Cauchy-Schwarz under \(h\,d\mu\) give
\[
 1\le a E\pi g \le a^2+C_{B,M}a\theta^{k+1}\sqrt V .
\]
It follows that \(\|g-1\|_2\le C_{B,M}\theta^k\), including \(V=0\). The set \(D_k=\{|g-1|>(2/3)^{k/8}\}\) has measure at most \(C_{B,M}(2/3)^{3k/4}\).

The [reference integrability estimate](POINTWISE-STABILITY-OF-SPECTRAL-RECOVERY.md) gives, for any ambient unit vector \(x\), uniform bounds \(C_B2^{33r}\) for both \(\|g_0^{-2}|Qx|^2\|_{21/20,\pi_0}\) and \(\||Qx|^2\|_{21/20,\pi_0}\). Its proof uses the reference quotient and \(\|\pi_0\|_2\le B\) alone. For any set \(D\), integrate the multiplier \(U\) using \(U= \pi_0g_0^{-2}(U/U_0)\). Hölder with \(42,21/20,42\) and \(\pi_0(D)\le B\mu(D)^{1/2}\) yields
\[
 E[\mathbf1_D U|Qx|^2]\le C_{B,M}2^{33r}\mu(D)^{1/84}.
\]
The same holds for \(\pi\) using \(s\). On the complement of \(D_k\) the multiplier difference has absolute value at most \(C(2/3)^{k/8}\pi\) for large \(k\). Taking \(D=D_k\) on the exceptional part and \(D\) equal to the full space to bound the good part proves \(\|QM_{U-\pi}Q\|\le C_{B,M}2^{33r}(2/3)^{k/112}\).

## The signed term without a pointwise envelope

For \(R=P_{2^{-1/4}}\) we need a bound on the full ambient operator \(RM_{|\pi-1|}R\). Take \(q=33/32\), and factor \(R=P_\lambda P_\gamma\) with \(\gamma^2=16/17,\ \lambda^2=17/(16\sqrt2)\). Ambient \(2\)-to-\(2q\) hypercontractivity and Jensen imply \(|Rx|^q\le P_\lambda|P_\gamma x|^q\) with input \(L^2\) norm at most one. The reference quotient weight \(\pi_0\) obeys the full multiplier estimate at \(s=2\), since \(1+4(16/17)^4\ge4\). Hence \(\||Rx|^2\|_{q,\pi_0}\le (B2^{r/2})^{1/q}\). Its conjugate exponent is \(33\), covered by \(\|s\|_{84,\pi_0}\). This gives \(\|RM_{|\pi-1|}R\|\le C_{B,M}2^{r/2}\) since \(|\pi-1|\le\pi+1\).

With \(Q=R^2\), split the inner \(R\) at degree \(\lfloor k/2\rfloor\). Two low terms vanish against \(\pi-1\) by matching. The other three terms together cost at most \(3C_{B,M}2^{r/2-(\lfloor k/2\rfloor+1)/4}\). Adding the first multiplier estimate gives the asserted bound for \(QM_UQ-P\). The two Gram products of \(M_{\sqrt U}Q\) have the same spectrum, and \(M_{\sqrt U}PM_{\sqrt U}\) is the stationary conjugate of the actual Doob kernel. This proves the full ordered comparison. The Markov bound covers small \(k\).

## Strict comparison of the two hypotheses at the same reference

Under the earlier pointwise log-ratio assumption the path estimate gives \(E_{\pi_0}\exp(168|\log u|)\le C\). Cauchy-Schwarz on the two coordinates of \(J_0\) then bounds \(E_{J_0}\xi^{\pm84}\). Thus that assumption implies the edge criterion.

For the converse test use uniform reference, \(n\) disjoint blocks of length \(m\ge2\), and the sets \(A_+,A_-\) on which all block parities equal \(+1,-1\), respectively. Each has uniform probability \(2^{-n}\). Set \(H=2^{n/336}\) on \(A_+\), \(H=2^{-n/336}\) on \(A_-\), and \(H=1\) elsewhere. Both \(H\) and \(H^{-1}\) have bounded \(L^{168}\) norms. The normalization \(Z=E HPH\) tends to one, since \((EH)^2\le Z\le EH^2\). Cauchy-Schwarz on the ordinary noise edge bounds both moments of \(\xi=H(x)H(y)/Z\) as claimed.

Given any starting point, independence of the noisy block parities yields \(P_x(A_\pm)\le[(1+2^{-m})/2]^n\le(5/8)^n\). Consequently \(PH=1+o(1)\) uniformly as \(n\to\infty\). The stationary law \(HPH/Z\) grows without bound on \(A_+\) and tends uniformly to zero on \(A_-\). It has exact matching through \(m-1\), since it is a function of the complete block parities. Let both \(n,m\) diverge. This verifies strict relaxation at the specified uniform reference; it makes no assertion about every possible alternative reference for this family.

As a negative control, for any set \(A\) and uniform reference, ordinary hypercontractivity gives \(J_0(A,A)=\langle\mathbf1_A,P\mathbf1_A\rangle\le\mu(A)^{4/3}\). If \(\pi\ge b>0\) and the tested law stays in \(A\) with probability at least \(1-\delta\) conditional on starting there in stationarity, then
\[
 \|\xi\|_{p,J_0}\ge b(1-\delta)\,\mu(A)^{(4-p)/(3p)},\qquad p>1.
\]
This follows by Hölder on the edge event. Every \(p>4\) therefore detects the [published rare metastable shell](https://airr.science/papers/ARR-2026-2B2W1WQ7DF9N5VW7/versions/v1/) through diverging positive edge moments, even though its vertex density approaches one in cubic mean. The bound at \(p=4\) alone does not prove divergence there. Neither 4 nor 84 is asserted to be the optimal threshold for recovery.

This subsequent analytic supplement is tied to the manuscript source at 4184d9cf423f974101af1fa1059218c04025cc64. No new grade, independent review, public deposit or worldwide priority claim is attached to it. A next test for the same endpoint problem is whether the exponent gap can be reduced using only positive edge moments and a stationary floor for the tested law relative to a nonuniform structured reference.
