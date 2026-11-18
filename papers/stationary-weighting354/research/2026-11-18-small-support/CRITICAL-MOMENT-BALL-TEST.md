# A critical moment test below the half-radius boundary

Fix correlation \(1/2\) on the Boolean cube with uniform probability. Write \(g=Ph\), \(\pi=hg\), \(U=h/g=\pi/g^2\). For each fixed \(0\le\alpha<1/2\) there exists \(c_\alpha>0\) such that, on every nonempty subset \(A\) of a Hamming ball of radius \(\alpha L\),
\[
 \|K_{AA}\|_{2\to2,\nu}\le e^{-c_\alpha L}\|\mathbf1_A U\|_3.
\]
The inequality holds with no floor, cap or matching assumption. The critical moment on the right remains a hypothesis when applying it to the original stationary class. In particular subexponential growth of that moment suffices at every fixed sub-half radius. This is a research note subsequent to the frozen assessed PDF.

## One coordinate

Use probability norms, \(p=3/2,\ q=3\). Set \(D_t(j)=\exp(t(1/2-j))\) for \(j=0,1\), and \(T_t=D_tPD_t\) in one dimension. Its \(p\)-to-\(q\) norm \(N(t)\) equals the supremum of \(\langle f,T_t f\rangle\) over \(f\ge0,\|f\|_p=1\). Positivity of the kernel allows absolute values in the dual bilinear expression, and positive semidefiniteness gives Cauchy–Schwarz for the bilinear form.

At \(t=0\) the unique nonnegative maximizer is the constant one. To see strictness, scale a nonzero pair and permute its entries to write them as \(1+x,1-x\), \(0\le x\le1\). Its noise energy is \(1+x^2/2\). Set \(F(x)=((1+x)^{3/2}+(1-x)^{3/2})/2\) and \(G(x)=(1+x^2/2)^{3/4}\). Both equal one at zero. Since \(\sqrt{1+x}+\sqrt{1-x}\le2\), one has \(F'(x)\ge3x/4>G'(x)\) for \(x>0\). Thus the energy is strictly less than the squared \(p\)-norm for each nonconstant pair.

The first derivative at zero of \(\langle1,T_t1\rangle\) vanishes since \(E(1/2-j)=0\). For any \(t_n\downarrow0\), compactness and uniqueness force normalized nonnegative maximizers \(f_n\) to approach one. The first-order Taylor remainder of the quadratic form in \(t\) is uniformly \(O(t^2)\) on the unit sphere. Comparing \(\langle f_n,T_0 f_n\rangle\le1\) with testing \(T_{t_n}\) on one proves \(\log N(t)=o(t)\) as \(t\downarrow0\).

## Tensor product and weight

For \(p\le q\), the \(p\)-to-\(q\) bound of a tensor power is at most \(N(t)^L\). In two factors apply the second operator for each first coordinate and the first operator for each second output coordinate. Minkowski gives \(\|u\|_{L_y^q L_x^p}\le\|u\|_{L_x^p L_y^q}\); iteration proves the assertion. The reverse lower bound follows on pure tensors, although only the upper bound is needed.

By translation take the center to be zero. For \(f\) supported in the ball, \(\|(D_t^{\otimes L})^{-1}f\|_p\le e^{-t(1/2-\alpha)L}\|f\|_p\). Therefore
\[
 \langle f,P^{\otimes L}f\rangle\le
 \left(N(t)e^{-2t(1/2-\alpha)}\right)^L\|f\|_{3/2}^2,
\]
where \(P\) in this display is the one-coordinate kernel. A small \(t>0\) depending only on \(\alpha\) makes the bracket strictly below one; define \(c_\alpha\) as minus its logarithm. Apply this to \(f=\sqrt U\,v\), using \(\|f\|_{3/2}\le\|\mathbf1_A U\|_3^{1/2}\|v\|_2\). Conjugating the actual killed kernel by its stationary square root gives the first inequality.

## What a falsifier would require

If a fixed-\(\alpha\) sequence has killed norms \(e^{-o(L)}\), then along that sequence \(\|\mathbf1_A U\|_3\ge e^{c_\alpha L-o(L)}\). With \(E\pi^3\le2\), this forces \(\inf_A g\le 2^{1/6}e^{-c_\alpha L/2+o(L)}\). Neither a large pointwise ratio nor a small pointwise denominator alone establishes slow escape. At \(\alpha=1/2\), the constant potential gives a killed norm at least \(1/2\), by the indicator test and the constant Walsh coefficient. This checks the strict upper boundary. The stationary floor plus cubic cap alone at all sub-half radii remains the one active question.

Small-support improvements of Boolean hypercontractivity are prior work. The elementary two-point tilt above is specialized to balls, and the Doob consequence is a conditional test. No global priority determination or independent formal verification is claimed. [Polyanskiy and Samorodnitsky, 2019](https://arxiv.org/abs/1606.07491).

