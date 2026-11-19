# Metastability at every fixed positive noise correlation

Subsequent analytic note to the half-noise manuscript at e5927d659a142f33a658eecc7f187657925c0090. It lies outside that manuscript's assessment. Group these extensions into its next substantive version.

**Claim.** Fix \(0<\rho<1\) and \(s=(1+\rho)/(1-\rho)\). There exist \(\varepsilon,\beta,c,d>0\), depending on \(\rho\), and radial potentials for every sufficiently large dimension \(L\), with the following properties. For each prescribed \(0<b<1\) their stationary density eventually exceeds \(b\) everywhere, \(\|\pi-1\|_{s+\varepsilon}\le e^{-cL}\), and every nonconstant Walsh coefficient up to degree \(\lfloor\beta L\rfloor\) vanishes. The normalized weighting moment \(\|r\|_s\) grows at least as \(e^{cL}\), while the gap of the actual Doob chain is at most \(e^{-cL}\). A sphere whose magnetization tends to \(d\) has exponentially small stationary mass and exponentially small exit probability from each of its points. Constants are fixed before taking dimension to infinity; no endpoint uniformity is used.

## Return probability and simultaneous choices

Let \(I(z)=((1+z)\log(1+z)+(1-z)\log(1-z))/2\) and
\[
 J_\rho(d)=\tfrac{1+\rho}{2} I(2d/(1+\rho))-I(d).
\]
Take the number of plus signs nearest \(L(1+d)/2\), giving target magnetization \(d_L=d+O(1/L)\). Write \(S\) for that exact sphere and \(q\) for its one-row ordinary return probability. For a stationary product noise edge the two equal-sign probabilities are \(a=(1+\rho)/4\) each and the unequal-sign ones \(z=(1-\rho)/4\) each. For the joint type, put the same integer nearest \(zL\) in both off-diagonal cells, then choose the two diagonal counts to give the prescribed plus and minus margins. All counts are nonnegative for \(d\) small and \(L\) large. These frequencies differ by \(O(1/L)\) from \((a+d/2,z,z,a-d/2)\). Relative entropy is smooth in a neighborhood of this strictly interior vector for fixed \(\rho,d\). The joint empirical event costs \(\exp[-L(1+\rho)I(2d/(1+\rho))/2-O(\log L)]\). Division by \(\mu(S)\le e^{-LI(d)+O(1)}\) yields
\[
 e^{-LJ_\rho(d)-O(\log L)}\le q\le e^{-(1-\rho)^2d_L^2L/2}.
\]
The upper bound uses the landing mean \(\rho d_L\) and the sign-average Hoeffding inequality. Rounding both off-diagonals together works for irrational \(\rho\) and all large \(L\).

Taylor expansion gives \(I(d)=d^2/2+O(d^4)\) and \(J_\rho(d)=I(d)/s+O_\rho(d^4)\). Let \(w=\rho^2(1-\rho)d/100,\ k=d^3\), and \(p_0=1+\rho^2(s-1)<s\). Since \(1/p_0-1/s>0\), fixing \(d>0\) sufficiently small ensures
\[
 J_\rho(d)-I(d)/s<k/2,\qquad J_\rho(d)+k<I(d)/p_0.
\]
In addition \(k/d^2\) can be made smaller than any prescribed positive constant depending only on \(\rho\), including all the concentration constants below. These choices use one common \(d\).

## Uniform lower bound, moment and survival

Center three bands \(B,C,D\) respectively at \(\rho d_L,\rho^2d_L,d_L\) with half-widths \(w,2w,2w/\rho\). They are disjoint and lie in \(m\ge \rho^2 d/2\) for large \(L\) since successive separations are \(\rho(1-\rho)d_L\) and \((1-\rho)d_L\). Define \(H_0=e^{-kL}\) on \(B\), \(e^{kL}\) on \(C\cup D\), and one elsewhere. Set \(M=e^{-kL/2}/q\) and \(H=H_0+M1_S\).

From \(B\) the landing mean is within \(\rho w\) of the center of \(C\), leaving a margin of at least \(w\). Outside \(D\) the landing mean is farther than \(2w\) from the center of \(B\); its chance to land in \(B\) is exponentially small. On \(D\) use \(H_0\ge e^{kL}\), \(PH_0\ge e^{-kL}\). Thus \(H PH\ge1-O(e^{-c_1L})\) everywhere. From \(S\), \(PH_0\le e^{-kL}+2e^{kL-w^2L/2}\), so each actual exit probability is \(O(e^{-kL/2})\). Take \(2k<w^2/2\). The upper bound on \(q\) ensures \(M\ge e^{kL}\) by decreasing \(d\) if necessary.

The union of bands has mass at most \(e^{-\rho^4 d^2L/8}\), so \(\|H_0PH_0-1\|_s\le(1+e^{kL})e^{kL}\mu(B\cup C\cup D)^{1/s}\) decays, choosing \(2k<\rho^4d^2/(8s)\). Off \(S\), the added stationary product has norm at most \(e^{kL}M\|P1_S\|_s\le e^{kL}M\mu(S)^{1/p_0}\) by ordinary hypercontractivity. On \(S\), use \(\|1_S HPH\|_s\le6e^{-kL}\mu(S)^{1/s}/q\). The two strict inequalities on \(J_\rho\) imply exponential decay in both estimates. Energy normalization therefore gives \(\|\pi_0-1\|_s\le O(e^{-c_2L})\) and \(\inf\pi_0\ge1-o(1)\).

Subtract the low Walsh coefficients for a fixed \(\beta>0\) with binary entropy less than \(c_2/2\). The uniform correction has norm \(O(e^{-c_2 L/2})\). The positive scaling inverse in section 4 of the half-noise manuscript uses only positivity, positive diagonal, and the positive semidefinite product kernel at positive correlation. It therefore reconstructs a radial potential whose log differs from the normalized precursor by \(O_b((L+1)e^{-c_2L/2})\). This preserves the rowwise exit estimate and the centered-indicator gap bound. The resulting density has \(\|\pi-1\|_s\le O(e^{-c_3 L})\). On a cube with atoms \(2^{-L}\), for \(p>s\),
\[
 \|f\|_p\le 2^{L(1/s-1/p)}\|f\|_s .
\]
Choose \(p=s+\varepsilon\) so that \((1/s-1/p)\log2<c_3/2\). This gives the strictly supercritical stationary convergence asserted above. The argument does not establish convergence in every finite moment.

## Divergence of the normalized critical weighting norm

In the tilted two-point argument now set \(p=1+\rho,\ q'=p/(p-1)\), and let \(T_t=D_t P_\rho D_t\), where \(D_t(j)=\exp(t(1/2-j))\) on \(j=0,1\). As in section 5 of the half-noise manuscript, the \(p\)-to-\(q'\) norm is the supremum of the quadratic form over nonnegative unit \(p\)-vectors. At zero its unique maximizer is one: a mean-one pair \(1\pm x\) has energy \(1+\rho x^2\). For \(0<x<1\) the derivative of \(F=((1+x)^p+(1-x)^p)/2\) is at least \(p\rho x\), because convexity of \(y^{\rho-1}\) gives \(\int_{1-x}^{1+x}y^{\rho-1}dy\ge2x\). The derivative of \((1+\rho x^2)^{p/2}\) is strictly less. Continuity includes \(x=1\). The normalized constant has vanishing first tilt derivative, so compactness gives \(\log\|T_t\|=o(t)\) at \(0^+\). Tensorization by Minkowski and both inverse tilt factors yield
\[
 \langle f,P_\rho f\rangle\le e^{-a_{\alpha,\rho}L}\|f\|_{1+\rho}^2
\]
for \(f\) supported on a ball of radius at most fixed \(\alpha L,\ \alpha<1/2\). For the rounded spheres choose \(\alpha=(1-d/2)/2\), which contains all sufficiently large targets. Apply this estimate to \(f=\sqrt U\,v\). Hölder uses \(1/(1+\rho)=1/2+1/(2s)\), forcing \(\|1_SU\|_s\ge e^{a_{\alpha,\rho}L}(1-o(1))\) from the retention Rayleigh quotient.

Finally \(g^{-1}\le Pg/b,\ Pg=P_{\rho^{3/2}}P_{\sqrt\rho}h\), with \(\|P_{\sqrt\rho}h\|_2=1\). Thus \(\|g^{-1}\|_{1+\rho^{-3}}\le1/b\). Since \(2s/(s-1)=1+\rho^{-1}\le1+\rho^{-3}\), \(\E U\le\|\pi\|_s/b^2\) is bounded. This proves the divergence of the normalized weighting moment.

## Verification and next test

The basis normalization, joint-type rounding, strict exponent slack, off-shell input exponent, shifted band widths, multiplier dual exponent and inverse-denominator moment have been checked analytically within the preparation context. The primary sources for the classical inputs are [Bonami](https://doi.org/10.5802/aif.357), [Hoeffding](https://doi.org/10.1080/01621459.1963.10500830) and [Polyanskiy and Samorodnitsky](https://arxiv.org/abs/1606.07491). This extension makes no independent priority or formal-check claim. A bounded next test is the fixed stationary moment \(7/2\) at half noise, between the perturbative extension above and stronger regularity regimes. Determine which side of the construction/upper-bound boundary it occupies before forming a new paper.

