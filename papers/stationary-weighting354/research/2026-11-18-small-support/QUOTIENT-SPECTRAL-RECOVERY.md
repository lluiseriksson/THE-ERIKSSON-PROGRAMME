# Full spectral recovery from four disjoint information sets

Consider the uniform binary cube, half-noise \(P=P_{1/2}\), \(Q=P_{1/\sqrt2}\), and a positive potential \(h\) normalized by \(E hPh=1\). Write \(g=Ph,\ \pi=hg,\ U=h/g\). The transition kernel is \(K(x,y)=P(x,y)h(y)/g(x)\). Matching to order \(k\) means that the nonconstant ambient Walsh coefficients of \(\pi\) vanish through degree \(k\).

**Theorem.** Suppose that \(\|\pi\|_2\le B\) and \(\pi(x)\) depends only on \(Ax\), where \(A:\mathbb F_2^L\to\mathbb F_2^d\) is onto. Suppose four pairwise disjoint sets of columns of \(A\) each form a basis of \(\mathbb F_2^d\). For all \(1\le k\le L\) with matching to order \(k\),
\[
 \max_j |\lambda_j(K)-\lambda_j(P)|\le C_B\,2^{-k/28}.
\]
Eigenvalues are ordered with multiplicity on the entire ambient cube. Neither a uniform positive floor for \(\pi\) nor a restriction on \(L\) in terms of \(k\) is needed. Strict positivity at each finite dimension is assumed.

## The stationary equation and the quotient

If \(h_1Ph_1=h_2Ph_2\) for two positive functions, write \(m=\min h_2/h_1,\ M=\max h_2/h_1\). If \(m<M\), the ratio \(Ph_2/Ph_1\) is strictly between \(m\) and \(M\) at every point, since all entries of \(P\) are positive. Its values at a maximizing and minimizing point for the first ratio would give both \(mM<1\) and \(mM>1\). Thus \(h_2=h_1\). Translations by \(\ker A\) preserve \(\pi\), hence preserve \(h,g,U\).

On quotient functions, ambient noise \(P_\lambda\) acts by independent additions of the columns of \(A\), each with probability \((1-\lambda)/2\). The operators commute. Each basis gives one ordinary \(d\)-bit noise operator in its own coordinates. Four successive basis factors therefore obey the forward and reverse Boolean hypercontractive curves at effective correlation \(\lambda^4\). Indeed each forward step multiplies the excess of the output exponent over one by \(\lambda^{-2}\). Each reverse step multiplies one minus the input exponent by \(\lambda^{-2}\), with geometric means used at exponent zero. The remaining columns are uniform-measure-preserving averages. They contract positive \(L^p\) norms for \(p\ge1\) and increase generalized means of positive functions for orders below one by Jensen. The forward and sharp reverse two-point inequalities are classical. [Bonami](https://www.numdam.org/articles/10.5802/aif.357/) and [Borell](https://doi.org/10.1007/BF01318906).

A positive quotient multiplier \(W\ge0\) obeys a corresponding **full-space** inequality. The operator \(P_\lambda M_W P_\lambda\) commutes with all kernel translations. When \(W\ne0\) and \(0<\lambda<1\), its matrix is strictly positive. Its top unit eigenvector is positive, unique up to sign and invariant under the translations. The top eigenvalue can therefore be computed on the quotient. For \(1<s<\infty\),
\[
 \|P_\lambda M_W P_\lambda\|_{2\to2}\le\|W\|_s
 \quad\text{if}\quad 2s/(s-1)\le 1+\lambda^{-8}.
\]
This is Hölder on the quotient followed by the forward estimate. For signed weights the associated absolute bilinear form is bounded by Cauchy-Schwarz with the absolute weight. This argument retains non-quotient eigenmodes in the final spectral comparison.

## An inverse moment without a stationary floor

Set \(F=Qh,\ a=Eh,\ V=1-a^2\). Then \(\|F\|_2=1,\ EF=a,\ \|F-a\|_2=\sqrt V\). Since \(g=QF\), its degrees above \(k\) have \(L^2\) norm at most \(2^{-(k+1)/2}\sqrt V\). Matching, the moment cap and Cauchy-Schwarz under \(h\,d\mu\) give
\[
 1=(Ehg)^2\le a E\pi g
 \le a^2+a B\,2^{-(k+1)/2}\sqrt V .
\]
Thus \(\sqrt V\le aB\,2^{-(k+1)/2}\), also when \(V=0\). In particular \(a\ge(1+B^2)^{-1/2}\) and \(\|g-1\|_2\le C_B 2^{-k/2}\).

Interpolation of positive moments gives \(\|F\|_{1/2}\ge a^3\), since \(\|F\|_2=1\). At \(Q\), four basis factors have squared effective correlation \(1/16=(1-1/2)/(1+7)\). Reverse hypercontractivity from \(1/2\) to \(-7\) gives
\[
 \|g^{-1}\|_7\le a^{-3},\qquad
 \|U\|_{14/11}\le B a^{-6}.
\]
The second estimate uses \(U=\pi/g^2\) and \(11/14=1/2+2/7\). The inverse moment follows from the actual stationary equation and noise structure.

Write \(E_k=\{|g-1|>2^{-k/8}\}\). Chebyshev gives \(\mu(E_k)\le C_B 2^{-3k/4}\). On its complement, \(|U-\pi|\le C2^{-k/8}\pi\) for sufficiently large \(k\). Restricted to \(E_k\), Hölder gives
\[
 \|\mathbf1_{E_k}(U-\pi)\|_{6/5}
 \le C_B\,\mu(E_k)^{5/6-11/14}
 =C_B\,\mu(E_k)^{1/21}.
\]
The full-space multiplier bound applies at \(Q\) with \(s=6/5\) since \(12\le17\). Hence \(\|QM_{U-\pi}Q\|\le C_B 2^{-k/28}\).

## The signed stationary term and the whole spectrum

Let \(R=P_{2^{-1/4}}\), so \(Q=R^2\). For \(W=|\pi-1|\) the full-space bound applies at \(R\) with \(s=2\) since \(4\le5\). Consequently \(\|M_{\sqrt W}R\|\le\sqrt{B+1}\). In \(Q\), split the inner \(R\) into ambient Walsh degrees up to \(j=\lfloor k/2\rfloor\) and above \(j\). The high part has norm at most \(2^{-(j+1)/4}\). The two low factors against \(\pi-1\) give zero, since their product has degree at most \(2j\le k\). Bounding the three remaining bilinear terms by the preceding weighted norm gives
\[
 \|QM_{\pi-1}Q\|\le 3(B+1)2^{-(j+1)/4}.
\]
This proves the bound for \(QM_UQ-P\). The two Gram products of \(M_{\sqrt U}Q\) have the same spectrum with multiplicity, and \(M_{\sqrt U}P M_{\sqrt U}\) is the stationary conjugate of \(K\). Min-max proves the theorem. Small \(k\) are covered by increasing \(C_B\), since both kernels have spectrum in \([0,1]\).

## An explicit regime beyond the earlier block estimate

For \(n\) disjoint length-\(m\) parities, the columns of \(A\) comprise \(m\) copies of each standard basis direction. For \(m\ge4\) there are four disjoint bases, and all nonzero codewords have weight at least \(m\). Matching through \(m-1\) is automatic. The theorem gives full spectral convergence for arbitrary growth of \(n\) if the second moment is uniformly bounded. The earlier disjoint-block proposition in [manuscript 354](../../manuscript354.tex) proved gap convergence for unrestricted positive potentials under \(n2^{-m}\to0\).

For example take \(n=2^m+1\), let \(S\in\{-1,1\}\) be the majority sign of the \(n\) block parities, and let \(H=1+(1-1/m)S\). Majority uses every block. The normalization \(Z=E HPH\) is at least \((EH)^2=1\) by positive semidefiniteness. Thus \(\pi=HPH/Z\le4\), while on the negative-majority region \(\pi\le2/m\). Both the old block-count condition and a uniform positive floor fail in this example. This also illustrates why the rescaling of \(h=H/\sqrt Z\) is necessary.

The general endpoint for stationary laws lacking the quotient symmetry remains open. A simple check on that remaining case is \(P_x(g\le t)\le t\,g(x)/b\) if \(\pi\ge b\): on the indicated set \(h=\pi/g\ge b/t\) and \(P_xh=g(x)\). This controls a bare-noise row probability. The row of \(K\) contains the additional factor \(h(y)/g(x)\), so the inequality by itself gives no small bound for the weighted return. A concrete next test is whether the full-space positive-multiplier estimate survives a small perturbation of a quotient stationary law, and in which norm.

This is an analytic research note subsequent to the frozen v2. The hypercontractive inequalities and the earlier matching-energy argument are inputs. No independent review, formal verification or worldwide priority claim is recorded for the new conclusion.
