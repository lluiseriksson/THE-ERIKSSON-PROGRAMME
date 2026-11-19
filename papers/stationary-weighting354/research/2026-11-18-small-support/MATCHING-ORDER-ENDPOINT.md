# A sparse exceptional set gives spectral recovery at the sufficient endpoint

Let \(P=P_{1/2}\) on the uniform binary cube of dimension \(L\), \(Q=P_{1/\sqrt2}\), \(g=Ph,\ \pi=hg,\ U=h/g\). Normalize \(E\pi=1\). Assume \(\pi\ge b>0,\ \|\pi\|_p\le B\) with \(p=p_*=(17+4\sqrt{13})/9\), and exact vanishing of all nonconstant Walsh coefficients of \(\pi\) through degree \(k\), \(1\le k\le L\). No symmetry of \(h\) is required.

**Result.** There are constants \(C,A,c>0\) depending only on \(B,b\) such that the maximum absolute difference of corresponding ordered eigenvalues of the Doob chain and \(P\) is at most
\[
 C e^{-ck}+ C(L/k)^A e^{-c k^2/L}.
\]
For \(k\ge\beta L\) this is exponential for each fixed \(\beta>0\). More generally \(k\ge D\sqrt{L\log(2L)}\) with a sufficiently large fixed \(D=D(B,b)\) gives convergence. This is a partial resolution of the endpoint question in Section 7 of the integrated manuscript. It leaves arbitrary slowly increasing orders unresolved.

## Cost of approaching the critical multiplier norm

The iteration in Section 7.1 of the revision at commit 1b24d36de2f0596e915fc605a86d52dc25bdf8c8 yields
\[
 q_0=9,\quad q_{j+1}=F(q_j)=16pq_j/(p+q_j)-9,\qquad
 \|g^{-1}\|_{q_{j+1}}\le (B/b)\|g^{-1}\|_{q_j}.
\]
This constant follows before taking any limits: bound \(h=\pi/g\) by Hölder, \(g\) by forward hypercontractivity, \(1/h\) by \(g/b\), and \(1/g\) by reverse hypercontractivity. Start with \(\|1/g\|_9\le1/b\). At the endpoint \(q_c=6p/(p-3)\) is fixed. Since \(F\) is increasing, concave, and \(F(9)>9\), the sequence increases to \(q_c\) (the graph is strictly above the diagonal in \([9,q_c)\)). Further \(F'(q_c)=16((p-3)/(p+3))^2<1\), as \(3<p<7/2\). After a fixed finite transient the distance to \(q_c\) decays geometrically. By Hölder \(1/t_j=1/p+2/q_j\) gives \(\|U\|_{t_j}\le B\|g^{-1}\|_{q_j}^{2}\). To reach \(t_j\ge3-\delta\) takes at most \(C_0+C_1\log(1/\delta)\) steps. Thus for \(0<\delta\le\delta_0\),
\[
 \|U\|_{3-\delta}+\|\pi\|_{3-\delta}\le C\delta^{-A}.
\]
This polynomial loss does not require a uniform critical norm.

## An arbitrary exponentially small set

Write \(m=k/L\). With \(\|g-1\|_2^2\le C2^{-k}\) by the matching-energy estimate (Section 7.2), \(E_k=\{|g-1|>2^{-k/8}\}\) has \(\mu(E_k)\le e^{-c_0 k}\) for all sufficiently large \(k\), for some fixed \(0<c_0<\log 2\). The estimates below apply to any set of this measure. For a nonzero function supported there and any \(a\in[1.4,1.5]\), Hölder gives \(\|f\|_a/\|f\|_1\ge e^{(1-1/a)c_0k}\).

Use Polyanskiy and Samorodnitsky, Theorem 7 and Remark 3, [arXiv:1606.07491](https://arxiv.org/pdf/1606.07491), at time \(T=(\log 2)/2\). Take the entropy parameter \(r=\eta m\) with \(0<\eta<(1-1/1.4)c_0\). This is strictly interior to the theorem's parameter range. Their ODE for the output exponent \(1+e^{u(t)}\) has \(u(0)=\log(a-1)\) and \(u'=C_{\rm PS}(r(1+e^{-u}))\). Here \(C_{\rm PS}\) is increasing, and \(C_{\rm PS}(x)\ge2+c_1 x\) on \([0,\eta]\) for some \(c_1>0\). To check strict linear gain at zero, parameterize \(x=I(z)=z^2/2+z^4/12+O(z^6)\). The numerator in the defining ratio is \(2-2\sqrt{1-z^2}=z^2+z^4/4+O(z^6)\). Hence \(C_{\rm PS}(x)=2+x/3+O(x^2)\); reduce \(\eta\) if needed. Monotonicity gives output exponent at least \(1+2(a-1)e^{c_1\eta T m}\). Set \(a=3/2-\sigma m\) for a sufficiently small fixed \(\sigma>0\) (in particular \(\sigma<0.1\)). This lower bound is at least two, uniformly for \(0<m\le1\): choose \(2\sigma\le1-e^{-c_1\eta T}\) and use concavity of \(1-e^{-c_1\eta T m}\). By positivity the result also applies to signed inputs. We obtain \(\|Qf\|_2\le\|f\|_a\) on \(E_k\).

Choose \(\delta=\delta_1m\) with \(0<\delta_1\le\delta_0\) sufficiently small. Set \(t=3-\delta,\ a'=2t/(t+1)\), so \(1/a'=1/2+1/(2t)\). This symbol denotes the Hölder product exponent, not the conjugate of \(a\). Since \(3/2-a'=\delta/(2(4-\delta))\), we can ensure \(1/a-1/a'\ge c_2 m\). For \(W=\mathbf1_{E_k}|U-\pi|\), apply the supported estimate to \(f=\sqrt W z\) and then Hölder twice:
\[
 \|Q(\sqrt W z)\|_2
 \le \mu(E_k)^{1/a-1/a'}\|\sqrt W z\|_{a'}
 \le e^{-c_3 k^2/L}\|W\|_t^{1/2}\|z\|_2 .
\]
The zero-measure case is immediate. Squaring the operator estimate and using adjoints bounds \(\|Q M_W Q\|\) by \(C m^{-A} e^{-c k^2/L}\), and quadratic form domination bounds the signed exceptional multiplier as well.

## Completion and limitation

On the complement of \(E_k\), \(|U-\pi|\le C2^{-k/8}\pi\), and \(\|\pi\|_3\le B\). Ordinary \(2\)-to-\(3\) hypercontractivity of \(Q\) controls this multiplier in the quadratic form. The term \(Q M_{\pi-1}Q\) is exponentially small in \(k\) by the low/high Walsh split of Section 7.2 applied with \(p=p_*>3\) to \(\pi\) alone. Consequently \(QM_UQ-P\) satisfies the displayed bound. The two Gram products and min-max identify the ordered eigenvalues as in the manuscript. Small \(k\) are absorbed in \(C\) by contraction of both Markov kernels. For the stated square-root-log regime use \((L/k)^A\le L^A\) and take \(cD^2>A+1\).

All estimates are analytic. This note is subsequent to the frozen v2 PDF and its first assessment. It uses the support-dependent improvement for an arbitrary set, so no Hamming ball enclosure of the bad set is assumed. For \(k\ll\sqrt L\), the gain in this proof can tend to zero even before the polynomial loss. No conclusion of failure of spectral recovery follows in that regime.
