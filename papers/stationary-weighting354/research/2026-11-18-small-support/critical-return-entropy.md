# How many syndromes can carry a persistent return?

Research supplement to the local-return criterion. All logarithms below are base two. This is an analytic result for finite chains, at the two-base critical moment \(p=15/7\).

Let \(P\) be product noise with correlation \(1/2\) on a binary cube with uniform probability \(\mu\). Let \(A\) have rank \(r\ge1\) and two disjoint column bases. Suppose the positive potential \(h\) depends only on the syndrome \(Ax\), put \(g=Ph,\ \pi=hg\), and assume \(\mathbb E_\mu\pi=1,\ \|\pi\|_{15/7}\le B\). The chain has kernel \(K(x,y)=P(x,y)h(y)/g(x)\) and stationary law \(\nu=\pi\mu\). Write \(T=M_{\sqrt U} P M_{\sqrt U}\), where \(U=h/g\). Conjugation by the square root of the stationary mass takes \(K\) to \(T\) on counting space. Thus \(0\le T\le I\) in quadratic-form order.

## A bound for a union of fibers

For any nonempty set \(S\) of syndromes define \(I_S=\log(2^r/|S|)\), \(D_S=1_{\{Ax\in S\}}\) as a multiplication operator, and \(Z=\sum_u 2^{-|A^\top u|}\), summed over the dual syndrome space. There is a constant depending only on \(B\) such that
\[
 \log \|D_ST D_S\|\ \le\ \log Z-\tfrac25 I_S+C_B\sqrt{1+I_S}.
\]
In particular, if \(|S|\le 2^{\beta r}\) for a fixed \(\beta<\beta_*=1-\tfrac52\log(5/4)=0.19517976\ldots\), the norm is exponentially small in \(r\). The same bound holds after restriction to any subset of these fibers, including cuts that split the fibers.

**Proof.** Fourier inversion on the quotient gives \(p_{00}=2^{-r}Z\) for the raw probability of staying at a syndrome. Every other transition probability \(p_{ij}\) is at most \(p_{00}\) by the triangle inequality on the same Fourier sum. By translation symmetry the block from fiber \(j\) to fiber \(i\) of the ambient \(P\) has all row sums and column sums equal to \(p_{ij}\). Its counting-space norm is at most \(p_{ij}\) by the Schur bound. For a unit vector supported on these fibers let \(a_i\) be its norm on fiber \(i\). Then
\[
 \langle f,Tf\rangle\le p_{00}\Big(\sum_{i\in S}\sqrt{U_i}\,a_i\Big)^2
 \le p_{00}\sum_{i\in S}U_i=Z\,\mathbb E_\mu[U D_S].
\]
Here expectation of the multiplier means expectation of its defining function. For each of the two column bases, its dual coordinates give a permutation of the binary cube. Dropping all other columns and applying Cauchy–Schwarz to the two basis factors in \(Z\) yields \(Z\le(1+1/4)^r\). This bound is attained for two identical bases with distinct column indices.

For transparency, keep track of the blowup of inverse moments at the endpoint. Since \(\|P^{1/2}h\|_2^2=1\) and \(P\) is a positive contraction, \(\|g\|_2\le1\). The set with \(\pi\ge1/2\) has measure at least \(1/(4B^2)\) by Cauchy–Schwarz. Removing \(g>4B\) leaves a set of measure at least \(b=3/(16B^2)\) where \(h\ge1/(8B)\). Each column basis contributes a full Boolean noise step at correlation \(1/2\) in its own coordinates. Twice applying Boolean reverse hypercontractivity gives
\(\|g^{-1}\|_q\le8B\,b^{-16/(15-q)}\), \(0<q<15\). Indeed the starting order \(a=(15-q)/16>0\) becomes \(1-4(1-a)\) and then \(-q\); any remaining column noise increases the negative-order norm by Jensen. This is the reverse estimate in the companion proof with its constants retained. [Companion proof](fractional-basis-recovery.tex) · [Mossel, Oleszkiewicz and Sen, Remark 1.13](https://arxiv.org/abs/1108.1210)

Use \(U=\pi g^{-2}\) and Hölder with reciprocals \(7/15,2/q,1-7/15-2/q\). Choose \(q=15-(1+I_S)^{-1/2}\in[14,15)\); all three reciprocals are positive. Relative to the limiting coefficient \(2/5\), the loss multiplying \(I_S\) is \(2(15-q)I_S/(15q)\). Both this loss and the logarithm of the inverse-moment constant are bounded by \(C_B\sqrt{1+I_S}\). Substitution proves the bound, including the stated exponential regime.

## What a persistent cut must look like

For any unit vector \(f\) on the ambient counting space let \(R=\langle f,Tf\rangle\) and \(\rho_i=\sum_{Ax=i}|f_x|^2\). For any syndrome set \(S\),
\[
 \sum_{i\notin S}\rho_i\ \ge\
 \big(\sqrt R-\sqrt{\|D_ST D_S\|}\big)_+^2.
\]
Apply the triangle inequality to \(T^{1/2}f\), bounded on the two pieces by \(\sqrt{\|D_ST D_S\|}\|D_S f\|\) and \(\|(1-D_S)f\|\). In particular for any cut \(E\) with \(\nu(E)>0\), take \(f_x=1_E(x)\sqrt{\nu(x)/\nu(E)}\). Then \(R=\Pr_\nu(X_1\in E\mid X_0\in E)\) and \(\rho\) is precisely the syndrome law conditional on \(E\).

Along any sequence \(r\to\infty\) with fixed \(B\) and \(\liminf R\ge s>0\), every set of at most \(2^{\beta r}\) syndromes leaves at least \(s-o(1)\) of the conditional mass outside, for each fixed \(0<\beta<\beta_*\). In particular
\[
 \liminf_{r\to\infty} H(\rho)/r\ \ge\ s\beta_* .
\]
To see this choose the largest \(\lfloor2^{\beta r}\rfloor\) atoms. Each remaining atom has mass at most the reciprocal of this count. Its entropy contribution is at least its mass times the logarithm of the count. Take the liminf first and then let \(\beta\) increase to \(\beta_*\). Adding many atoms of negligible total mass cannot defeat this test. The coefficient is a sufficient exclusion threshold; its optimality for Doob chains is open.

## Consequence for ordered recovery

Under the additional order-\(k\) marginal matching hypotheses and the exceptional multiplier cutoff of the [floor-free local-return criterion](local-return-floor-free.tex), if the exceptional set lies over at most \(2^{\beta r}\) syndromes with fixed \(\beta<\beta_*\), its killed norm is exponentially small in \(r\). The criterion gives ordered recovery with error \(O_B(e^{-ck}+e^{-c' r})\), with constants also depending on the fixed cutoff and \(\beta\). If the exceptional set is empty the killed term is zero. The proof of the cut estimate itself uses no matching, pointwise stationary lower bound, symmetry between the two bases, or formal-verification claim.

The remaining question is whether matching and a bounded critical moment can support a returning cut whose conditional entropy grows linearly in rank. A sequence satisfying both hypotheses with return bounded below inside the exceptional set would refute unconditional recovery. Counting syndromes alone cannot settle that remaining case.
