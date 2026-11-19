# Critical multipliers on rare sets of the Boolean cube

Use uniform probability \(\mu\) on \(\{-1,1\}^L\). Let \(Q=P_{1/\sqrt2}\) be the Boolean noise operator, \(M_W\) multiplication by \(W\), and
\[
 S_L(s)=\sup\{\|QM_W Q\|_{2\to2}: W\ge0,\ \|W\|_3\le1,\ \mu(W>0)\le e^{-s}\}.
\]
Here \(s\) is the logarithmic rarity of a set, measured using the natural logarithm. In the earlier endpoint estimate it is proportional to the matching order \(k\). The multiplier problem itself imposes no marginal constraints.

**Proposition.** For \(1\le s\le L/32\) there is a universal constant \(c>0\) such that
\[
 (1-e^{-s})e^{-16s^2/L}\ \le\ S_L(s)\ \le\ e^{-cs^2/L}.
\]
In particular \(S_L(s)\to1\) when \(s\to\infty\) and \(s=o(\sqrt L)\). It tends to zero when \(s/\sqrt L\to\infty\) in the stated range.

## Product witness at fixed noise time

Set \(r=1/\sqrt2,\ u=\sqrt{8s/L}\le1/2\), and use the unit vector
\[
 z(x)=\frac{\prod_{i=1}^L(1+u x_i)}{(1+u^2)^{L/2}},
 \qquad Qz(x)=\frac{\prod_{i=1}^L(1+r u x_i)}{(1+u^2)^{L/2}} .
\]
All factors are positive. Under the probability law with density \((Qz)^3/\|Qz\|_3^3\) the signs are independent, with mean
\[
 m=\frac{3ru+r^3u^3}{1+3r^2u^2}\ge u .
\]
The inequality follows from \(3r/(1+3r^2/4)>1\). Put \(A=\{\sum_i x_i\ge mL/2\}\). The bounded-sign Hoeffding inequality on each side of the threshold gives
\[
 \mu(A)\le e^{-Lm^2/8}\le e^{-s},\qquad
 \frac{\int_A(Qz)^3\,d\mu}{\|Qz\|_3^3}\ge 1-e^{-s}.
\]
Take \(W=\mathbf1_A Qz/\|Qz\|_3\). Then \(\|W\|_3\le1\) and the Rayleigh quotient on \(z\) is at least \((1-e^{-s})\|Qz\|_3^2\). For \(v=u^2\) the exact one-coordinate calculation gives
\[
 L^{-1}\log\|Qz\|_3^2=\tfrac23\log(1+3v/2)-\log(1+v)=:\ell(v).
\]
Since \(\ell(0)=0\) and \(\ell'(v)=-v/[2(1+3v/2)(1+v)]\), this is at least \(-v^2/4\). Substitution proves the lower bound with the given constant. This calculation uses the fourth-order loss in \(u\) at the ordinary hypercontractive exponents.

## Upper bound and dependence on the moment assumption

The sparse-input consequence of Polyanskiy and Samorodnitsky proved in the [preceding endpoint note](MATCHING-ORDER-ENDPOINT.md) gives an absolute \(\sigma>0\) and \(a=3/2-\sigma s/L\) for which \(\|Qf\|_2\le\|f\|_a\) whenever \(\mu(\mathrm{supp}\,f)\le e^{-s}\). For clarity, in their Theorem 7 use time \(\log(2)/2\) and entropy parameter \(\eta s/L\) for sufficiently small fixed \(\eta>0\). Hölder supplies this parameter on the support; the output exponent exceeds two by choosing \(\sigma\) small using \(C_{\rm PS}(x)=2+x/3+O(x^2)\). For \(f=\sqrt W y\), a second use of Hölder gives
\[
 \|Q(\sqrt W y)\|_2
 \le e^{-s(1/a-2/3)}\|\sqrt W y\|_{3/2}
 \le e^{-s(1/a-2/3)}\|W\|_3^{1/2}\|y\|_2 .
\]
Squaring the operator norm and using \(1/a-2/3\ge(4\sigma/9)s/L\) proves the upper bound. The sparse hypercontractivity input and its short-time optimality statement are due to [Polyanskiy and Samorodnitsky, Theorem 7 and Remarks 3–4](https://arxiv.org/pdf/1606.07491). The lower calculation above concerns a weighted quadratic form at one fixed positive time. No claim of literature-wide priority is made.

**Corollary for the endpoint proof.** Fix \(A_0>0\). If \(s\to\infty,\ s\le L/32\), and \(16s^2/L\le A_0\log s\), there exist nonnegative radial multipliers \(V\) satisfying, simultaneously,
\[
 \mu(V>0)\le e^{-s},\qquad
 \|V\|_{3-\delta}\le C_{A_0}\delta^{-A_0}\quad(0<\delta\le1),\qquad
 \|QM_VQ\|_{2\to2}=1 .
\]
Indeed set \(N=\|QM_WQ\|>0\) for the explicit witness and \(V=W/N\). The lower bound gives \(N^{-1}\le (1-e^{-s})^{-1}s^{A_0}\). On its support,
\[
 \|W\|_{3-\delta}\le \exp[-s(1/(3-\delta)-1/3)]\le e^{-s\delta/9}.
\]
The uniform bound now follows by maximizing \(x^{A_0}e^{-x/9}\) over positive \(x=s\delta\). Normalization gives the claimed spectral norm exactly. One can take \(s=D\sqrt{L\log L}\) for any fixed \(D>0\) with \(16D^2<A_0/2\), for sufficiently large \(L\). This matches the order, up to constants, of the sufficient scale in the previous note for the abstract rarity and moment estimates. It does not prove that the actual Doob-chain threshold has this order.

## How the true chain constrains the next construction

For an actual chain the quantities also satisfy \(g=P_{1/2}(Ug)\) and \(\pi=Ug^2\). As a concrete check, simply adding a positive constant to the witness \(V\) and normalizing its Perron root cannot give a nonconstant chain with exactly uniform one-coordinate marginals. The witness is coordinatewise increasing. For any strictly positive increasing \(U\), the positive operator \(P_{1/2} M_U\) preserves nonnegative increasing functions by the monotone Bernoulli coupling. Starting from one and normalizing the iterates gives its positive Perron vector \(g\), which is increasing. Thus \(\pi=Ug^2\) is increasing. For each coordinate \(i\), \(E[\pi x_i]\) is half the mean of the nonnegative difference between the two coordinate slices. Exact matching forces that difference to vanish on every edge in that direction. Matching each singleton therefore makes \(\pi\) constant, and positivity and monotonicity of both factors force \(U\) constant as well. Dividing a weight by its Perron root does not change this argument.

The open question remains spectral recovery at \(p_*=(17+4\sqrt{13})/9\) for arbitrary diverging matching order in the actual chain. The explicit multipliers close the route based solely on set measure and polynomial subcritical moments. A remaining test is to use the equation for \(g\) to control the weighted mass of transitions between different low-\(g\) levels. The frozen eight-page v2 manuscript and its first assessment predate this note.
