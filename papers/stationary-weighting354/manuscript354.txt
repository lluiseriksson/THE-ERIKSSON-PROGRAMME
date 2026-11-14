Stationary-to-weighting moment transfer and spectral rigidity for Boolean Doob kernels
Lluis Eriksson
14 November 2026. Working paper
Plain text; mathematical expressions retain TeX notation.
No PDF assessment or publication implied.

ABSTRACT

For positive potentials on a Boolean cube, the stationary density of the noise Doob kernel and its normalized weighting density are different nonlinear functions of the potential. We give an admissible family for which the stationary critical moment is below two while the weighting critical moment is above two, despite a fixed positive stationary floor and exact marginals through order proportional to the square root of the dimension. This refutes transfer of that numerical cap, not the existence of a larger uniform bound. A nonlinear consequence of the stationary floor, combined with classical ordinary and reverse hypercontractivity, gives explicit inverse-potential moments and weighting-moment bounds below a computable finite threshold. Exact stationary matching then gives strong convergence of the two densities throughout this subcritical range. For potentials supported on a binary linear-code Fourier algebra, we control every invariant sector of the full Doob kernel. Under a distance--cardinality condition its gap tends uniformly to the unweighted gap, for every positive quotient potential. Direct disjoint-block estimates cover a sharper parameter regime. A standard simplex code supplies positive potentials outside the disjoint-block class. Classical random linear coding extends this mechanism to positive-rate families at every sufficiently large length, with an explicit exponential gap estimate and normalized witnesses meeting any fixed stationary floor below one and the moment cap. The general stationary-gap question and critical weighting-moment bound remain open.




Setting and theorem map

Let $\mu$ be uniform probability on $\{-1,1\}^L$, $L\geq1$, and let $0<\rho<1$ be fixed. Boolean product noise is denoted by $P=P_\rho$, with $P_\rho\chi_S=\rho^{|S|}\chi_S$ for Walsh characters $\chi_S$. Unqualified expectations and norms use $\mu$. For $h>0$ set
\[
 g=Ph,\quad Z=\E hg,\quad \pi=hg/Z,\quad
 N=\E(h/g),\quad r=(h/g)/N.
\]
Both $\pi$ and $r$ have mean one. The Markov kernel
\[
 K(x,y)=P(x,y)h(y)/g(x)
\]
is reversible for $\pi\,d\mu$. Its eigenvalues are positive: conjugation by multiplication by $\sqrt\pi$ identifies it with
$M_{\sqrt{h/g}}P M_{\sqrt{h/g}}$, a positive definite matrix. Its top eigenvalue is one and is simple because all entries are positive. Write $\lambda_2(K)$ for its second eigenvalue and $\operatorname{gap}(K)=1-\lambda_2(K)$. These are finite Markov-chain quantities.

The general question motivating this work fixes $b,C>0$, puts
\[
 s=\frac{1+\rho}{1-\rho},\qquad k_L=\min\{L,\lfloor C\sqrt L\rfloor\},
\]
and imposes
\begin{equation} [admissible] 
 \pi\geq b,\qquad \E\pi^s\leq2,\qquad
 \E\pi\chi_S=0\quad(1\leq |S|\leq k_L).
\end{equation}
The last condition concerns the actual stationary density, on the original labelled coordinates. It is equivalent to uniform coordinate marginals of these orders. It does not assign exact marginals to $r$.

Our results have four distinct scopes. Section 2 gives one fixed $\rho$ and floor for which the numerical implication $\E\pi^s\leq2\Rightarrow\E r^s\leq2$ fails even under all of \eqref{admissible}. Section 3 treats every fixed $\rho$ and proves a dimension-free bound for $\norm r_t$ for $1\leq t<t_+(\rho)<s$; with matching it proves $r-\pi\to0$ in this range. Section 4 treats every positive potential on specified code algebras, without a moment cap or floor for its spectral result. It controls the full chain, not only its quotient. Section 5 relates the sharper disjoint-block bounds and the simplex example to these conclusions. Section 6 proves positive-rate, all-large-length code existence with simultaneous column separation, specializes the full-chain estimate exponentially, and gives actual normalized stationary floor/cap witnesses.

The manuscript groups analytical sources 349, 350, 351, corrected 353B and 355. The total-variation estimate from source 341 is proved again in Section 3. No spectral conclusion is inferred from moment convergence alone. No assertion about a physical Yang--Mills gap or a continuum limit is made.



Failure of exact critical-cap transfer


theorem:  [capfailure] 
There are fixed $\rho_*\in(1/3,1/2)$ and $b_*=1/16$ such that, for every fixed $C>0$, a sequence of strictly positive potentials satisfies \eqref{admissible} for every $L$ and satisfies
\[
 \E\pi_L^{s_*}<2<\E r_L^{s_*}
 \quad\hbox{for all sufficiently large }L,
 \qquad s_*=(1+\rho_*)/(1-\rho_*).
\]
Both displayed moments tend to two. This is not a divergent-moment or collapsing-gap example.



Proof. 
On a two-dimensional cube, in the order $(++,+-,-+,--)$, take
\[
 H=(29/16,\ 1/4,\ 1/8,\ 29/16)
   =1+cx-cy+dxy,\qquad c=1/32,\quad d=13/16.
\]
Thus $\E H=1$. Put $q=c(x-y)$, $v=2c^2=1/512$, $w=d^2=169/256$. For an effective noise parameter $\theta\geq0$,
\[
 G_\theta=P_\theta H=1+\theta q+\theta^2dxy,
 \quad Z_\theta=\E HG_\theta=1+\theta v+\theta^2w.
\]
Take $h_\theta=H/\sqrt{Z_\theta}$, $\pi_\theta=HG_\theta/Z_\theta$, and
$r_\theta=(H/G_\theta)/\E(H/G_\theta)$. These are actual densities from the same potential. At $\theta=0$, both densities equal $H$, and differentiation gives
\[
 \pi'_0=H(q-v),\qquad r'_0=-H(q-v).
\]
Indeed $\E Hq=v$ and $(\E H/G_\theta)'_{\theta=0}=-v$. For each fixed $t>1$, let
\[
 C_t=\E H^tq-v\E H^t
 =\frac{31(1/4)^t-33(1/8)^t-2(29/16)^t}{2048}.
\]
This is strictly negative. To see this, $f(t)=31\,4^{-t}-33\,8^{-t}$ has
$f'(t)=\log2\,8^{-t}(99-62\,2^t)<0$ for $t\geq1$, whereas $2(29/16)^t$ is increasing; at $t=1$ both are $29/8$. Consequently
\begin{equation} [oppositederivatives] 
 \left.\frac{d}{d\theta}\E\pi_\theta^t\right|_0=tC_t<0,
 \qquad
 \left.\frac{d}{d\theta}\E r_\theta^t\right|_0=-tC_t>0.
\end{equation}

Let $M(t)=\E H^t$. Direct rational identities give
$M(2)=851/512<2$ and $M(3)=24425/8192>2$.
Strict convexity of $x\log x$ gives $M'(1)=\E H\log H>0$, and
$M''(t)=\E H^t(\log H)^2>0$. Thus there is a unique $t_*\in(2,3)$ with $M(t_*)=2$. Fix $\rho_*=(t_*-1)/(t_*+1)$, so its critical exponent is precisely $t_*$. Formula \eqref{oppositederivatives}, with this exponent fixed, gives strict opposite inequalities around two for all sufficiently small positive $\theta$. No varying exponent or numerical root is used.

For large $L$, let $m=\lfloor L/2\rfloor$ and use two disjoint blocks $B_1,B_2$ of size $m$, with an unused coordinate when $L$ is odd. Set $z_i=\chi_{B_i}$ and $\theta=\rho_*^m$. The variables $z_1,z_2$ are uniform and independent; restricted to their algebra, $P_{\rho_*}$ is exactly the two-bit $P_\theta$. Use $h_L=H(z_1,z_2)/\sqrt{Z_\theta}$. Products, positive inverses and expectations on the quotient agree with those above, so these are the required actual $\pi_L,r_L$.

Their Fourier support is contained in
$\{\varnothing,B_1,B_2,B_1\cup B_2\}$. In particular $\pi_L$ has exact marginals through degree $m-1$. Eventually $m>k_L$, $\theta\to0$, and $\min\pi_L\to\min H=1/8$. Choose a finite $L_0$ after which the floor $1/16$, the matching degree and the two strict moment inequalities all hold. For the remaining finitely many $L$, put $h_L=1$. This defines a full admissible sequence. Continuity gives convergence of both moments to two. Section 5 shows that this two-block family in fact has gap tending to $1-\rho_*$.
End of proof.


The following estimates distinguish two simpler classes: two-level potentials cannot produce divergent critical weighting moments under a fixed stationary floor and cap, while product potentials obey the stronger constant-one moment comparison.

proposition:  [simplefamilies] 
Normalize $\E hPh=1$ and assume $\pi\geq b$. If $h$ takes at most two values, then $g\geq b/2$ and
$\E r^p\leq(4/b^3)^p\E\pi^p$ for every $p\geq1$.
If $h$ is a product of positive one-coordinate factors, then $\E r^p\leq\E\pi^p$ for every $p\geq1$, without a floor assumption. The latter also holds for products of factors on disjoint block parities, with their respective effective noise parameters.



Proof. 
Write $a=\E h\leq1$, the inequality following from the constant Fourier component of $\norm{P_{\sqrt\rho}h}_2^2=1$. The floor implies $h\geq b/g$, so $a\geq b\E(1/g)\geq b/a$. Hence $a^2\geq b$. Under $\pi\,d\mu$,
$\E_\pi(1/g)=a$ and $\E_\pi(1/g^2)=N$, giving $N\geq a^2\geq b$.
For a nonconstant two-level $h$, let $h=m$ on a set of mass $q\in(0,1)$ and $h=M>m$ on its complement. Integrating the floor on the first set gives $m\E(g1_A)\geq bq$, whence $m\geq bq$. Also $M(1-q)\leq a\leq1$. Since $g\geq m$ and $hg\geq b$ with $h\leq M$, we get $g\geq\max\{bq,b(1-q)\}\geq b/2$. Thus $r=\pi/(Ng^2)\leq4\pi/b^3$. The constant case is immediate.

For one bit, scaling removes an irrelevant constant, so take $H=1+tx$, $|t|<1$. The normalized densities are $\pi=1+Ax$ and $r=1+Bx$, where
\[
 A=\frac{(1+\rho)t}{1+\rho t^2},\qquad
 B=\frac{(1-\rho)t}{1-\rho t^2}.
\]
Cross multiplication gives $|B|\leq|A|$, since the difference of the two relevant positive numerators is $2\rho(1-t^2)>0$. The function
$[(1+c)^p+(1-c)^p]/2$ is even and nondecreasing for $c\in[0,1)$ and $p\geq1$. This proves the one-bit assertion. Tensorization of the noise, the energy, $N$ and the moments proves the product assertions.
End of proof.




Inverse moments and subcritical transfer

In this section scale $h$ so $Z=1$, put $Q=P_{\sqrt\rho}$ and set $B=2^{1/s}$. Assume $\pi=hg\geq b>0$ and $\E\pi^s\leq2$; necessarily $b\leq1$. Define
\begin{align*}
 R&=1+\rho^{-1},&D_0&=1+\rho^{-3},&D_*&=2\rho^{-2}+\rho^{-3}-1,\\
 F(q)&=1+\frac{sq/(s+q)-1}{\rho^4},&&&
 q_\pm&=\frac{1+\rho}{\rho^3}\bigl(1+\rho^2\pm\sqrt{1+\rho^2}\bigr).
\end{align*}
Let $q_0=D_*$, $q_{n+1}=F(q_n)$, and
\[
 A_n=b^{-1}(B/b)^n,\qquad
 t_n=\frac{sq_n}{q_n+2s},\qquad t_+=\frac{sq_+}{q_++2s},\qquad
 K_n=Bb^{-3}(B/b)^{2n}.
\]

theorem:  [subcritical] 
For every $L$ and $n\geq0$,
\[
 N\geq b,\quad gPg\geq b,\quad
 \norm{g^{-1}}_{D_0}\leq b^{-1},\quad
 \norm{g^{-1}}_{q_n}\leq A_n,\quad \norm r_{t_n}\leq K_n.
\]
Here $q_-<D_*<q_+$, $q_n\uparrow q_+<\infty$, and
$1<t_0<t_n<t_+<s$ for $n>0$. These conclusions need no matching.
If additionally $\E\pi\chi_S=0$ for $1\leq|S|\leq k$, put
\[
 \eta_0=\sqrt{\max\{\rho,(1-\rho)/2\}}<1,
 \qquad e_k=B\eta_0^{k+1}.
\]
For $1<t<t_n$,
\begin{equation} [strongtransfer] 
 \norm{r-\pi}_t\leq (2e_k)^\alpha(K_n+B)^{1-\alpha},
 \qquad \alpha=\frac{t_n-t}{t(t_n-1)}.
\end{equation}
Thus for every fixed $1<t<t_+$, $\norm{r-\pi}_t\to0$ whenever $k\to\infty$, in particular for $k=k_L$.



We use the classical scalar Boolean hypercontractive inequalities \cite{mos}: for $1<p\leq q<\infty$, $\norm{P_\theta f}_q\leq\norm f_p$ when $\theta^2\leq(p-1)/(q-1)$. For strictly positive $f$ and finite $\beta<\alpha<0$, reverse hypercontractivity gives
$\norm{P_\theta f}_\beta\geq\norm f_\alpha$ when
$\theta^2\leq(1-\alpha)/(1-\beta)$. Negative exponents denote generalized means $(\E f^a)^{1/a}$, not norms. In particular $\norm f_{-a}=1/\norm{f^{-1}}_a$ for $a>0$. No zero-exponent convention is needed in the uses below.


Proof. 
The preceding proof gives $a=\E h\in[\sqrt b,1]$ and $N\geq b$. Applying $P$ to $h\geq b/g$ and using Jensen in each transition row yields
\begin{equation} [flooridentity] 
 g\geq bP(1/g)\geq b/(Pg),\qquad g^{-1}\leq(Pg)/b.
\end{equation}
This is a consequence of the actual stationary floor, not an assumed bound on $\inf g$.
Since $\norm{Qh}_2=1$ and $Pg=P_{\rho^{3/2}}Qh$, ordinary hypercontractivity gives $\norm{Pg}_{D_0}\leq1$, proving the first inverse bound. Likewise $g=P_{\sqrt\rho}Qh$ gives $\norm g_R\leq1$. The floor yields $h^{-1}\leq g/b$, so $\norm h_{-R}\geq b$. Reverse hypercontractivity with $\alpha=-R$, $\beta=-D_*$ and $\theta=\rho$ applies because
$D_*=(1+R)/\rho^2-1>R$. It gives $\norm g_{-D_*}\geq b$, or $\norm{g^{-1}}_{D_*}\leq b^{-1}$. Also $D_*-D_0=2(\rho^{-2}-1)>0$.

If $q>s/(s-1)$ and $\norm{g^{-1}}_q\leq A$, put $p=sq/(s+q)>1$. Holder applied to $h=\pi/g$ gives $\norm h_p\leq BA$. As $Pg=P_{\rho^2}h$, hypercontractivity and \eqref{flooridentity} give
\[
 \norm{g^{-1}}_{F(q)}\leq b^{-1}\norm{Pg}_{F(q)}\leq (B/b)A.
\]
The map has
\[
 F(q)-q=\frac{-\rho^4q^2+(s-1)(1-\rho^4)q-s(1-\rho^4)}{\rho^4(s+q)},
 \qquad F'(q)=\frac{s^2}{\rho^4(s+q)^2}>0.
\]
The numerator has roots $q_-,q_+$: its discriminant equals
$4\rho^2s(1-\rho^4)$, and $s(1-\rho^4)=(1+\rho)^2(1+\rho^2)$. Direct bounds show
\begin{align*}
 \rho^3(D_*-q_-)&=\rho-\rho^2-2\rho^3+(1+\rho)\sqrt{1+\rho^2}
 \geq(1+2\rho)(1-\rho^2)>0,\\
 \rho^3(q_+-D_*)&=-\rho+\rho^2+2\rho^3+(1+\rho)\sqrt{1+\rho^2}
 \geq1+\rho^2+2\rho^3>0.
\end{align*}
Since $D_*>R=2s/(s-1)$, every step is valid. Monotonicity of $F$ gives
$q_n<q_{n+1}<q_+$, and continuity identifies the limit as $q_+$. Iteration gives $A_n$. Finally
\[
 r=\frac{\pi}{Ng^2},\qquad \frac1{t_n}=\frac1s+\frac2{q_n}
\]
and Holder give $\norm r_{t_n}\leq b^{-1}BA_n^2=K_n$. The inequalities between the $t_n$ follow from $D_*>2s/(s-1)$ and monotonicity of $q\mapsto sq/(q+2s)$.
End of proof.


For completeness we supply the stationary matching argument underlying \eqref{strongtransfer}; it does not require a pointwise floor.

lemma:  [rigidity] 
Under energy normalization, if $\norm\pi_p\leq B_p$ for a finite $p>1+\rho$ and $\pi$ has exact marginals through degree $k$, set
$\eta_p^2=\rho\max\{1,1/(p-1)\}<1$ and $e=B_p\eta_p^{k+1}$.
Then $a^2\geq(1+e^2)^{-1}$, $a^2\leq N\leq1$, and $\norm{r-\pi}_1\leq2e$.



Proof. 
Put $v=1-a^2=\norm{Qh-a}_2^2\geq0$, and let $\Pi_{>k}$ be Walsh projection above degree $k$. We have
\[
 \norm{\Pi_{>k}g}_{p'}\leq\eta_p^{k+1}\sqrt v,\qquad p'=p/(p-1).
\]
For $p'\leq2$ this is the high-degree multiplier bound for $Q$, followed by norm monotonicity. For $p'>2$, factor $Q=P_tP_\beta$, where $t=1/\sqrt{p'-1}$ and $\beta=\sqrt\rho/t=\eta_p<1$. Hypercontractivity sends $P_t:L^2\to L^{p'}$, and the high-degree multiplier of $P_\beta$ supplies the stated bound. The noise operators commute with Walsh projections; no norm bound for the projection on $L^{p'}$ is presumed.
Matching gives $\E\pi\Pi_{\leq k}g=a$. Hence $\E\pi g\leq a+e\sqrt v$. Cauchy--Schwarz for the measure $h\,d\mu$ gives
$1=(\E hg)^2\leq a\E hg^2=a\E\pi g$. Therefore $v/a\leq e\sqrt v$. If $v>0$, division yields $v\leq a^2e^2$; the $v=0$ case is immediate. Thus $a^2\geq(1+e^2)^{-1}$ and $2(1-a)\leq e^2$.

For the upper bound on $N$, put $u=h/g$ and $A=M_{\sqrt u}PM_{\sqrt u}$. The positive vector $\sqrt{hg}$ has $A$-eigenvalue one. Perron--Frobenius and positive semidefiniteness therefore give $\norm A=1$. With $X=M_{\sqrt u}Q$, the matrices $XX^*=A$ and $X^*X=QM_uQ$ have the same eigenvalues. Testing the latter at the unit vector $1$ yields $N=\E u\leq1$. Cauchy--Schwarz under $\pi$ gives $a^2\leq N$ as above. Since $r=\pi/(Ng^2)$,
\[
 \E\sqrt{r\pi}=a/\sqrt N\geq a,\qquad
 \norm{\sqrt r-\sqrt\pi}_2^2=2(1-a/\sqrt N)\leq e^2.
\]
Multiply the difference of the square roots by their sum and apply Cauchy--Schwarz; the latter sum has norm at most two. This gives $\norm{r-\pi}_1\leq2e$. Total variation is half this $L^1$ distance, not the entire distance.
End of proof.



Proof. 
Apply Lemma \ref{rigidity} with $p=s>1+\rho$, $B_p=B$. Its parameter becomes $\eta_0$ in the theorem. Since $t_n<s$, $\norm{r-\pi}_{t_n}\leq K_n+B$. Interpolation between $1$ and $t_n$, with $1/t=\alpha+(1-\alpha)/t_n$, gives \eqref{strongtransfer}. For each fixed $t<t_+$ choose one finite $n$ with $t<t_n$ before taking $L\to\infty$.
End of proof.


The ceiling is a limitation of this particular iteration. Its starting exponent lies strictly between the two fixed points and increases only to finite $q_+$. Moreover $A_n=b^{-1}(B/b)^n$ diverges as $n\to\infty$. We have neither a uniform estimate at $q_+$ nor one at $t_+$. Even a finite inverse bound at $q_+$ would leave $t_+<s$. None of these facts disproves a different method for the critical moment.



Full-chain estimates for code-supported potentials

Identify Walsh indices with vectors in $\F_2^L$, and let $\mathcal C$ be a nonzero binary linear code of dimension $n$ and minimum nonzero Hamming weight $D\geq2$. Set $M=2^n$ and
\[
 \delta=\sum_{c\in\mathcal C\setminus\{0\}}\rho^{|c|}<1,
 \quad \eta=M\rho^{D/2},\quad \alpha=\frac{1-\delta}{1+\delta},
 \quad B_{\mathcal C}=\frac{\rho+\eta}{1-\delta},\quad
 \varepsilon_{\rm gap}=\frac{(1-\rho^2)\delta}{\rho(1-\delta)}.
\]

theorem:  [codetheorem] 
For every strictly positive $h$ whose Fourier support is contained in $\mathcal C$, with no size restriction on its quotient values,
\begin{equation} [codegap] 
 \max\{0,\rho-\varepsilon_{\rm gap}\}\leq\lambda_2(K)
 \leq\min\{1,\max\{1-\alpha,B_{\mathcal C}\}\}.
\end{equation}
Both $\pi$ and $r$ have exact marginals through degree $D-1$, and
\begin{equation} [codecompare] 
 \alpha^2\leq r/\pi\leq\alpha^{-2}.
\end{equation}
For any sequence of such codes with fixed $\rho$ and $\eta\to0$,
$\operatorname{gap}(K)\to1-\rho$, uniformly over all strictly positive quotient potentials. If additionally $\E\pi^s\leq2$, then $\E r^s\leq2\alpha^{-2s}$. The cap is needed for this absolute moment bound, not for \eqref{codegap} or \eqref{codecompare}.



Proof. 
Choose a basis $c_1,\ldots,c_n$ and put $z_i(x)=\chi_{c_i}(x)$. This quotient map is surjective with equal fibers, and $h(x)=H(z(x))$ for a positive function $H$. Writing $c(I)=\sum_{i\in I}c_i$, the quotient noise density relative to uniform $w$ is
\[
 b_0(z,w)=\sum_{I\subseteq[n]}\rho^{|c(I)|}\chi_I(z)\chi_I(w).
\]
This is the actual positive stochastic quotient of product noise. In particular
$1-\delta\leq b_0\leq1+\delta$. With $a=\E H$ and $G=P H$ on the quotient,
$a(1-\delta)\leq G\leq a(1+\delta)$. The quotient Doob kernel has density $b_0(z,w)H(w)/G(z)$ and minorizes $\alpha$ times the probability density $H(w)/a$. Thus its oscillation contraction is at most $1-\alpha$. Every nonconstant eigenfunction has nonzero oscillation, so all its non-Perron eigenvalues have modulus at most $1-\alpha$.

It remains to control the other sectors, because the quotient spectrum alone is insufficient. For each coset $t+\mathcal C$, let
$V_t=\chi_t\{F(z):F\hbox{ any quotient function}\}$. These spaces are mutually orthogonal under $\pi\,d\mu$: products of quotient functions with $\pi$ remain in the $\mathcal C$ algebra, and a Walsh character outside $\mathcal C$ has zero expectation against that algebra. They span all $2^L$ dimensions. Multiplication by $h$ and by $1/g$ preserves each sector, as does noise, so each is $K$-invariant.
Under the identification $\chi_t F\leftrightarrow F$, its operator is
\[
 K_tF(z)=\E_w\, b_t(z,w)\frac{H(w)}{G(z)}F(w),\qquad
 b_t(z,w)=\sum_I\rho^{|t+c(I)|}\chi_I(z)\chi_I(w).
\]
For $t\notin\mathcal C$ this is a signed kernel, not a Markov kernel. Choose a minimum-weight representative with $d=|t|\geq1$. If $d\leq D/2$, all other vectors in the coset have weight at least $D-d\geq D/2$, so
\[
 \sum_{v\in t+\mathcal C}\rho^{|v|}
 \leq\rho^d+(M-1)\rho^{D/2}\leq\rho+\eta.
\]
If $d>D/2$, all weights exceed $D/2$ and the sum is at most $\eta$. Consequently
$|b_t|\leq\rho+\eta\leq B_{\mathcal C}b_0$, whence
$|K_tF|\leq B_{\mathcal C}K_0|F|$. Supremum norms bound every sector eigenvalue in modulus by $B_{\mathcal C}$. Together with the quotient bound and the global Markov bound one this proves the upper inequality in \eqref{codegap}.

For the lower inequality, any singleton $e_i$ is outside $\mathcal C$ because $D\geq2$. In $b_{e_i}-\rho b_0$, a codeword not containing $i$ contributes zero; a codeword containing $i$ contributes coefficient
$(1-\rho^2)\rho^{|c|-1}$. Hence
\[
 |b_{e_i}-\rho b_0|\leq(1-\rho^2)\delta/\rho
 \leq\varepsilon_{\rm gap}b_0.
\]
It follows that $|K_{e_i}1-\rho|\leq\varepsilon_{\rm gap}$. The original character $\chi_{e_i}$ has mean zero under $\pi$ and norm one, since $\pi$ is in the $\mathcal C$ algebra. Its Rayleigh quotient is at least $\rho-\varepsilon_{\rm gap}$. The variational principle and positive definiteness yield the lower bound.

The algebra of quotient functions is closed under multiplication and positive inversion. Thus $\pi$ and $r$ are both $\mathcal C$-supported; their unit means imply the stated exact marginals. Let $\Pi=HG/Z$ be the quotient stationary density. Then
\[
 \E_\Pi G^{-2}=N/Z,\qquad r/\pi=\frac{G^{-2}}{\E_\Pi G^{-2}}.
\]
The interval $a(1-\delta)\leq G\leq a(1+\delta)$ proves \eqref{codecompare}. Finally
$\delta\leq(M-1)\rho^D\leq\eta\rho^{D/2}\leq\eta$. If $\eta\to0$, then $\delta\to0$, $\alpha\to1$, $B_{\mathcal C}\to\rho$ and $\varepsilon_{\rm gap}\to0$, uniformly in $H$. This proves the limiting and moment assertions.
End of proof.




Disjoint blocks and a strictly larger potential class



The sharper direct block regime

Let $L=nm+d$ with $n\geq1$, $m\geq2$ and $d\geq0$, and let $h=H(z_1,\ldots,z_n)>0$, where $z_i$ is the parity of the $i$th disjoint block of size $m$. Residual coordinates are unused. This is a special code algebra, but direct factorization yields better bounds than the coarse distance--cardinality estimate.

proposition:  [blocktheorem] 
Put $\theta=\rho^m$, $\ell=(1-\theta)^n$, $u=(1+\theta)^n$, and
\[
 \alpha_b=\ell/u,\qquad
 \beta_b=\frac{\rho+\rho^{m-1}}{1-\theta},\qquad
 \varepsilon_{\rm gap,b}=\frac{(1-\rho^2)\rho^{m-1}}{1-\theta}.
\]
For every positive $H$,
\[
 \max\{0,\rho-\varepsilon_{\rm gap,b}\}\leq\lambda_2(K)
 \leq\min\{1,\max\{1-\alpha_b,\beta_b\}\},\qquad
 \alpha_b^2\leq r/\pi\leq\alpha_b^{-2}.
\]
Both densities have exact marginals through degree $m-1$. If $m\to\infty$ and $n\rho^m\to0$, the gap tends uniformly in $H>0$ to $1-\rho$.



Proof. 
The quotient noise density is $b_0(z,w)=\prod_i(1+\theta z_iw_i)$, so $\ell\leq b_0\leq u$ and $a\ell\leq G\leq au$. The same minorization and moment arguments as in Theorem \ref{codetheorem} give the quotient and density bounds, now with $\alpha_b$.
For a sector representative, remove complete blocks from its support. Let $j_i\in\{0,\ldots,m-1\}$ be its number of coordinates in block $i$, and $e$ its residual weight. Factoring the Fourier sum gives
\[
 b_t(z,w)=\rho^e\prod_i\bigl(\rho^{j_i}+\rho^{m-j_i}z_iw_i\bigr).
\]
For $j_i=0$ the factor is that of $b_0$. If $1\leq j_i\leq m-1$, its absolute ratio to $1+\theta z_iw_i$ is bounded by $\beta_b$: the numerator is at most $\rho^{j_i}+\rho^{m-j_i}\leq\rho+\rho^{m-1}$. This last inequality follows because the convex function $x\mapsto\rho^x+\rho^{m-x}$ attains its maximum on $[1,m-1]$ at an endpoint. If $\beta_b<1$, a nontrivial sector with at least one interior factor therefore has $|b_t|\leq\beta_b b_0$; if it has only residual support, its ratio is $\rho^e\leq\rho<\beta_b$. This bounds those eigenvalues. If $\beta_b\geq1$, the global Markov bound one already gives the stated upper bound; no invalid inequality $\beta_b^j\leq\beta_b$ is used.

For a singleton in one block, its factor differs from $\rho(1+\theta z_iw_i)$ by $(1-\rho^2)\rho^{m-1}z_iw_i$. The other factors are unchanged, yielding
$|b_t-\rho b_0|\leq\varepsilon_{\rm gap,b}b_0$. The singleton Rayleigh argument gives the lower bound. All nonzero vectors in the block code have weight at least $m$, giving matching. Finally
$-\log\alpha_b=n\log[(1+\theta)/(1-\theta)]\leq4n\theta$ once $\theta\leq1/2$. Thus $\alpha_b\to1$, $\beta_b\to\rho$ and $\varepsilon_{\rm gap,b}\to0$ in the stated regime.
End of proof.


Structural inclusion must not be confused with inclusion of the quantitative regimes. Theorem \ref{codetheorem} applied to this code asks for $2^n\rho^{m/2}\to0$, whereas Proposition \ref{blocktheorem} requires only $n\rho^m\to0$ with $m\to\infty$. We retain the direct bounds instead of claiming the coarser condition subsumes them. In particular Proposition \ref{blocktheorem} with $n=2$ applies to Theorem \ref{capfailure}.



Simplex potentials outside disjoint-block representations


proposition:  [simplex] 
For each $j\geq2$ put $L_j=2^j-1$ and index coordinates by nonzero $v\in\F_2^j$. The binary simplex code
\[
 \mathcal C_j=\{c_a:a\in\F_2^j\},\qquad c_a(v)=a\cdot v,
\]
has dimension $j$ and every nonzero word has weight $D_j=2^{j-1}$. It satisfies the asymptotic condition in Theorem \ref{codetheorem} for every fixed $0<\rho<1$. On this length subsequence its matching degree eventually exceeds $\lfloor C\sqrt{L_j}\rfloor$ for every fixed $C>0$.
There are strictly positive potentials supported on this code that cannot be represented as functions of disjoint equal-size block parities of size $m\geq2$, even after coordinate permutations or enlargement of the disjoint-block algebra.



Proof. 
The map $a\mapsto c_a$ is injective by inspection at the unit-vector coordinates. A nonzero linear form takes the value one at exactly half the points of $\F_2^j$, and the excluded zero vector has value zero. Thus the dimension and weight assertions follow directly. Here
\[
 \delta_j=(2^j-1)\rho^{2^{j-1}},\qquad
 \eta_j=2^j\rho^{2^{j-2}}\longrightarrow0.
\]
In particular $\delta_j<1$ eventually. Also $D_j-1=(L_j-1)/2$, proving the matching assertion on the stated subsequence.

Choose
\[
 h_j=1+\varepsilon_{\rm amp}\sum_{c\in\mathcal C_j\setminus\{0\}}\chi_c,
 \qquad 0<\varepsilon_{\rm amp}<1/(2^j-1).
\]
This is strictly positive, and its Fourier support is exactly $\mathcal C_j$. The amplitude $\varepsilon_{\rm amp}$ is not the spectral error $\varepsilon_{\rm gap}$.
If $h_j$ were a function of disjoint block parities, uniqueness of the Walsh expansion would put $\mathcal C_j$ inside the linear span of those block indicators. Every word in that span is constant within each block and vanishes on unused coordinates. But $\mathcal C_j$ separates every pair of distinct coordinates $v,w$: choose $a$ with $a\cdot(v+w)=1$. Also every coordinate is nonzero in some codeword. Consequently no block can contain two coordinates and none can be unused. This contradicts $m\geq2$, and is unchanged by coordinate permutations or by allowing more disjoint blocks.
End of proof.


The code construction is classical \cite{wootters}; its elementary parameter proof is included to avoid treating a coding reference as a new theorem. The strict separation is an existence statement for the full-support positive potentials just exhibited. It does not hold for every potential in the code algebra, since constants also belong to disjoint-block algebras. Nor does this argument assert a prescribed stationary floor or moment cap for the displayed amplitude family. Its use here is to establish that the full-chain code theorem covers positive potentials beyond the disjoint-block class. Arbitrary invertible changes of the original Boolean coordinates are not permitted replacements for permutations: they generally change Hamming weights and the noise operator.



Positive-rate families at every sufficiently large length

The simplex example gives a transparent strict-class witness on a length subsequence. Classical random linear coding also realizes the spectral mechanism at positive rate for every sufficiently large length. The additional column conditions used below ensure strict separation from disjoint-block representations for the same codes, rather than for separately chosen examples.

Let $H_2(d)=-d\log_2d-(1-d)\log_2(1-d)$ denote binary entropy.

theorem:  [positiverate] 
Fix $0<\rho<1$, $0<d<1/2$ and
\begin{equation} [ratecondition] 
 0<R_{\rm code}<\min\left\{1-H_2(d),\ \frac d2\log_2(1/\rho)\right\}.
\end{equation}
For every sufficiently large integer $L$ there exists a binary linear code $\mathcal C_L\subset\F_2^L$ with dimension $n_L=\lfloor R_{\rm code}L\rfloor$, minimum distance $D_L\geq\lceil dL\rceil$, and a generator matrix with nonzero, pairwise distinct columns. Set
\[
 a_*=(d/2)\log(1/\rho)-R_{\rm code}\log2>0,\qquad
 E_L=e^{-a_*L},\qquad
 C_\rho=\max\{1+\rho,(1-\rho^2)/\rho\}.
\]
For every strictly positive potential $h$ supported on the Fourier algebra of this code, and all sufficiently large $L$,
\begin{equation} [exponentialgap] 
 \left|\operatorname{gap}(K_h)-(1-\rho)\right|
 \leq C_\rho\frac{E_L}{1-E_L}.
\end{equation}
The bound is uniform over all such positive $h$, with no amplitude, stationary floor or moment assumption. Both $\pi$ and $r$ have exactly uniform labelled marginals through degree $\lceil dL\rceil-1$.

Moreover, for every fixed $0<b<1$ and finite $s>1$, there are potentials in these same algebras, at every sufficiently large length, with energy one, $\pi\geq b$ and $\E\pi^s\leq2$, whose Fourier support is the full code and which admit no disjoint equal-size block-parity representation with block size at least two. In particular these witnesses satisfy \eqref{admissible} for its critical exponent and every fixed $C>0$, eventually, and have the gap estimate \eqref{exponentialgap}.



Proof. 
Both upper bounds in \eqref{ratecondition} are positive, so the allowed rate interval is nonempty. Put $n=\lfloor R_{\rm code}L\rfloor$, eventually at least one, and sample an $n$ by $L$ matrix $G$ with independent fair binary entries. This is a probabilistic existence argument, not an executed random search. For each fixed nonzero $a\in\F_2^n$, the entries of $aG$ are independent fair bits. The different vectors $aG$ need not be independent. A union bound gives
\[
 \Pr\{\exists a\ne0:\ |aG|<dL\}
 \leq(2^n-1)2^{-L}\sum_{0\leq i<dL}\binom Li
 \leq2^{n-L(1-H_2(d))}.
\]
For the last step, since $d<1/2$ and $i\leq dL$,
\[
 d^i(1-d)^{L-i}\geq d^{dL}(1-d)^{(1-d)L}=2^{-LH_2(d)}.
\]
Multiply this lower bound by $\binom Li$, sum over the stated integer indices, and bound the corresponding binomial probability sum by one. This proves the entropy bound without assuming $dL$ integral. The complement of the strict bad event gives weights at least $\lceil dL\rceil$. In particular a nonzero kernel vector is impossible, so $G$ has full row rank and its row-image code has dimension $n$.

Each column is uniform in $\F_2^n$. A second union bound gives
\[
 \Pr\{\hbox{a zero column or an equal pair of columns}\}
 \leq \left[L+\frac{L(L-1)}2\right]2^{-n}.
\]
The sum of these two error bounds tends to zero. Indeed the first is at most
$2^{-L(1-H_2(d)-R_{\rm code})}$ and the second is at most
$2[L+L(L-1)/2]2^{-R_{\rm code}L}$. For every sufficiently large integer $L$, their sum is less than one, so a single matrix has simultaneously the distance, rank and column properties. Select one for each such length. No efficient construction or nested family is asserted.

For the resulting code, $M_L=2^{n_L}$ and $D_L\geq dL$ give
\[
 \eta_L=M_L\rho^{D_L/2}\leq E_L,
 \qquad \delta_L\leq M_L\rho^{D_L}\leq\eta_L\leq E_L.
\]
Eventually $D_L\geq2$ and $\delta_L<1$, so Theorem \ref{codetheorem} applies to every positive code potential. For $E_L\leq\min\{1/2,\rho/2\}$,
\begin{align*}
 1-\alpha&=\frac{2\delta_L}{1+\delta_L}\leq2E_L\leq\rho,\\
 B_{\mathcal C_L}&=\frac{\rho+\eta_L}{1-\delta_L}
 \leq\rho+(1+\rho)\frac{E_L}{1-E_L},\\
 \varepsilon_{\rm gap}&\leq\frac{1-\rho^2}{\rho}\frac{E_L}{1-E_L}.
\end{align*}
The two sides of \eqref{codegap} therefore give \eqref{exponentialgap}; the clipping by zero and one only improves the estimates. The matching assertion follows from the same theorem and $D_L\geq\lceil dL\rceil$. In particular this matching degree eventually exceeds $\lfloor C\sqrt L\rfloor$ for every fixed $C>0$.

It remains to construct the admissible strict-class witnesses. Nonzero columns ensure that every coordinate is active in some codeword; distinct columns ensure that every two coordinates are separated by some codeword. For the latter, if the two columns are $v\ne w$, choose a linear functional detecting $v+w\ne0$.
For $0<\tau<1$, choose
\[
 h_0=1+\frac{\tau}{M_L-1}\sum_{c\in\mathcal C_L\setminus\{0\}}\chi_c.
\]
Then $1-\tau\leq h_0\leq1+\tau$, and its Fourier support is exactly $\mathcal C_L$. If $h_0$ were a function of any number of disjoint equal-size block parities, its full support would force $\mathcal C_L$ into the span of their whole-block indicators. Every word in that span is constant within a block and zero on unused coordinates. Pair separation excludes any block of size at least two, and activity excludes residual coordinates. This rules out every representation allowed in Proposition \ref{blocktheorem}, including larger quotient algebras and coordinate permutations.

For prescribed $0<b<1$ and finite $s>1$, choose $\tau>0$ sufficiently small that
\[
 A_\tau=\left(\frac{1+\tau}{1-\tau}\right)^2
 \leq\min\{1/b,2^{1/s}\}.
\]
The right side exceeds one, so such a single positive $\tau$, independent of $L$, exists. Positivity and the Markov property put both $h_0$ and $Ph_0$ in $[1-\tau,1+\tau]$. Hence their product and its mean $Z$ lie in $[(1-\tau)^2,(1+\tau)^2]$. Set $h=h_0/\sqrt Z$. This preserves its support and kernel, gives $\E hPh=1$, and yields
\[
 A_\tau^{-1}\leq \pi=\frac{h_0Ph_0}{Z}\leq A_\tau,
 \qquad \pi\geq b,\qquad \E\pi^s\leq A_\tau^s\leq2.
\]
Thus all assertions concern the same normalized potential and its actual stationary density. The full-chain bound was already uniform in the potential and remains valid for these witnesses.
End of proof.


The entropy-volume and random-linear-code ingredients are classical Gilbert--Varshamov arguments \cite{guruswami}; the proof is included with the precise rounding and simultaneous column requirements used here. The rate $R_{\rm code}$ is distinct from the inverse-moment exponent $R$ of Section 3. The theorem supplies all-large-length positive-rate realizations of the code-restricted mechanism. It does not remove the code-algebra hypothesis, establish a general critical weighting cap, or provide a collapsing example. The strict-class conclusion is existential for the specified full-support potentials, not universal for all positive functions on the code. The prescribed-floor witness assertion excludes $b=1$ and makes no uniform endpoint claim as $\rho$ approaches zero or one.




Positioning, failed routes and remaining question

Ordinary and reverse hypercontractivity are classical tools. Mossel, Oleszkiewicz and Sen explicitly state the Boolean reverse inequality, including negative exponents and tensorization, in equation (1.2) \cite{mos}. The use here is the floor-derived identity $gPg\geq b$ and its particular exponent iteration; we do not claim a new hypercontractive inequality. Representation-based decomposition of reversible chains is also classical; Boyd, Diaconis, Parrilo and Xiao discuss commuting symmetries and spectral reduction \cite{boyd}. Our sector estimates explicitly retain all cosets and compare their signed kernels to the quotient kernel. The binary simplex construction is not original. Entropy-volume estimates and random-linear-code existence are classical Gilbert--Varshamov tools; the simultaneous column condition used here is verified directly rather than attributed as an extra clause of the coding theorem \cite{guruswami}.

The bounded primary check supporting this draft reads the relevant statements just cited, not the entire related literature. Targeted searches did not establish the priority of the specific moment counterexample, the quantitative iteration or the uniform code-potential estimates. Search results about ``Doob graphs'' concern a different object from the Doob transform used here and do not establish overlap or novelty. The results in this draft are proved as stated; mathematical correctness, originality and relevance remain separate questions. No claim of first discovery or frontier classification is made.

The evidence supplement preserves unsuccessful routes rather than replacing their records. Proposition \ref{simplefamilies} excludes divergent critical weighting moments for two-level potentials and exact-cap failure for product potentials. The finite fixed point in Section 3 obstructs only the specified iteration. Theorem \ref{capfailure} refutes the exact numerical cap, while its own moments remain bounded and its gap remains asymptotically unweighted. A generic pair of densities close in total variation is not a counterexample unless both arise from the same $h$ and satisfy the stationary hypotheses.

The historical source 353A had a false strict-class-separation claim based on three disjoint blocks $A,B,C$ and the code generated by $A\cup B$ and $B\cup C$. Its two quotient coordinates can indeed be written as products of the three disjoint block parities, so every such potential already belongs to the larger three-block algebra allowed in Proposition \ref{blocktheorem}. The corrected source 353B preserves that failed claim and its adverse audit, keeps the valid core code theorem, and substitutes the simplex witness of Proposition \ref{simplex}. Lack of a disjoint basis for one chosen code is not enough to prove absence of a larger disjoint-block representation.

The single remaining research question is whether \eqref{admissible}, at fixed $\rho,b,C$, forces a uniformly positive full-chain gap or allows an admissible collapsing family. One unresolved bridge is a finite dimension-independent bound on $\E r^s$. Under energy normalization,
\[
 \E r^s=N^{-s}\E\bigl[\pi^s g^{-2s}\bigr],\qquad N\geq b.
\]
The portion with $g>1$ is controlled by the stationary cap. The joint small-$g$ contribution is not controlled at the critical exponent by the finite inverse moments above. Additional exact matching has been used to obtain strong subcritical convergence, not to settle this endpoint. Even an endpoint moment bound would still require a justified spectral argument for the general question. The code theorem excludes a concrete structured family of collapsing mechanisms, not all stationary densities satisfying \eqref{admissible}.



Model assessments and review context

This source manuscript is a new consolidation, not a reviewed PDF. No PDF has been produced from 354B, and no exact-PDF model assessment, numerical grade, peer-review decision, acceptance or publication is asserted. Earlier analytical sources 349, 350, 351, corrected 353B and 355 received separate-role source audits that the programme parent accepted; those audits do not certify this newly assembled manuscript or any future rendered PDF.

The manuscript preparation is by the involved fabrication role in the same provider workflow. This role previously developed sources 349 and 350 and consolidation 352; the parent supplied the bootstrap lead in source 350, authored sources 351, 353A and 355, and supplied the corrected simplex witness in 353B. The source auditor had relevant prior exposure, including the adverse scope finding on 353A. These are disclosed dependencies, not independent-model replications. The user requested the Astra high alias; the exact serving backend is not independently attested in this preparation, and no model version is inferred from that request. Full source reports, contexts, objections, failed drafts and byte manifests are retained in the accompanying evidence packet.

Only analytical derivation and document/source handling were performed for this consolidation. No mathematical program, numerical experiment, formal proof, local compilation or runtime result is claimed. Classical external results are attributed, and their bounded reading scope is recorded. Draft354A was frozen before source355 was incorporated and remains preserved; it was not separately manuscript-audited before this revision. The retained source hashes identify the mathematical inputs; the manuscript has its own hash and requires its own separate source audit before document production and exact-PDF review.


REFERENCES

[mos] E. Mossel, K. Oleszkiewicz and A. Sen, \emph{On reverse hypercontractivity}, arXiv:1108.1210v5 (2012), introduction, equations (1.1)--(1.2). \url{https://arxiv.org/pdf/1108.1210}.
[boyd] S. Boyd, P. Diaconis, P. Parrilo and L. Xiao, \emph{Symmetry Analysis of Reversible Markov Chains}, author-hosted manuscript revised 29 November 2004, introduction and symmetry setup. \url{https://web.stanford.edu/~boyd/papers/pdf/symmetry.pdf}.
[wootters] M. Wootters, \emph{CS250/EE387: Error Correcting Codes}, Problem Set 1, Winter 2025, Section 2.4 (simplex-code construction). \url{https://web.stanford.edu/class/archive/cs/cs250/cs250.1254/Homework/HW1/hw1.pdf}.
[guruswami] V. Guruswami, \emph{Introduction to Coding Theory, Notes 2: Gilbert--Varshamov bound}, CMU, January 2010, Lemma 5 and Theorem 8, including their proofs. \url{https://www.cs.cmu.edu/~venkatg/teaching/codingtheory/notes/notes2.pdf}.


