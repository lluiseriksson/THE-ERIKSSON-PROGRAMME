# Exact packet-averaged multiplier and volume-density transport

Status: analytic proof, NOT a new Lean endpoint. This note composes the exact actualVolumeMean_nonlinear_rank endpoint at mathematical SHA3a2d5305df4ec817c2ec9739e269272d6b29967d (paired reproduction091/091b) with elementary exact sums and a limit argument. Parent main a3c83d5f1fe8e3c2e1eb51ac4c2ca6550a043258 includes that proof through checked PR135. No numerical experiment is used as a proof.

## 1. Domain, retained original hypotheses and frequency conventions

Put D=d+2>=2. Fix Nc>=2 and n,R integers with R>=1 and 2R<n. The actual frequency indices defined by coexactPositiveFourierIndex have first signed lift k_0=1,...,R, and every other lift k_j=-R,...,R, independently. This is the product of a POSITIVE first-coordinate interval and D-1 centered intervals, not a transverse diagonal slice. Both real quadratures q in Bool are included. Their actual real dimension is

H=2R(2R+1)^(D-1).

All original local hypotheses of actualVolumeMean_nonlinear_rank remain: actual flat gauge background and divergence-free domain; C:E_n->F_n differentiable at0 with derivative L and C(0)=0; finite-dimensional real F_n; Phi(y)<=K||y||^2 for ||y||<delta, delta>0; positive original coercivity radius; repaired coercivity with coefficient c on those small fields. In addition, m>=0 bounds the occupied coefficient means in EVERY direction i and l=0,1:

sum_x max(1+w_n(i,x,l),0) <= n^D m.

Original w_n is signed, without any original-weight lower bound; other field components need no mean restriction. Signed means alone do not suffice. In the following rank rearrangement c>0 is required; the preceding formal finite endpoint itself only required c>=0.

Write q_n=dim_R F_n. The verified endpoint gives

c(H-q_n) <= m S,
S=sum_(k,q) sum_(j=0,...,D-1) |exp(2pi i k_j/n)-1|^2.

The actual Fourier character evaluates to that exponential because its ZMod frequency is the reduction of the signed integer lift. Negative lifts are NOT replaced by large wrapped ZMod.val values. |exp(it)-1|^2=4sin^2(t/2) follows directly from cos^2+sin^2=1. The stencil has all D coordinate directions; field support on components0,1 does not remove the other D-2 derivative directions.

## 2. Exact finite average

Let x=pi/n, A_R(x)=sum_(r=1,...,R) sin^2(rx), and B_(D,R,n)=S/H. Then

B_(D,R,n)=4 A_R(x) [1/R + 2(D-1)/(2R+1)]
            =4 A_R(x) (2DR+1)/(R(2R+1)).                 (1)

Proof by counting: for j=0 each positive r has (2R+1)^(D-1) index choices and two quadratures. Its contribution to S/H is 4A_R/R. For each fixed j>0, each signed k_j has R(2R+1)^(D-2) index choices and two quadratures. Since sin^2 is even and vanishes at0, its signed-coordinate sum is 2A_R. Each such direction contributes 8A_R/(2R+1). There are D-1 such directions. This counts every index and both quadratures once.

For n>=3, sin x>0. The exact trigonometric sum is

A_R(x)=R/2 - sin(Rx)cos((R+1)x)/(2sin x).               (2)

An independent telescoping derivation avoids treating a library identity as an assumption. For each r,

2sin x cos(2rx)=sin((2r+1)x)-sin((2r-1)x).

Sum r=1,...,R. The right side telescopes to sin((2R+1)x)-sin x. The sine subtraction formula then gives

sum_r cos(2rx)=sin(Rx)cos((R+1)x)/sin x.

Using sin^2(rx)=(1-cos(2rx))/2 proves (2). These are classical finite geometric/Dirichlet-kernel identities, not claimed new general results.

Substituting (1) in the checked finite rank endpoint and dividing by positive c gives the exact-symbol quantitative consequence

q_n >= H [1-(m/c) B_(D,R,n)].                         (3)

A negative right side is simply a weak lower bound. One may combine it with q_n>=0. For R=0 the actual packet is empty and the verified inequality is trivial; formulas involving 1/R are not asserted there.

## 3. Sharper elementary quadratic estimate

Since |sin t|<=|t| and sum_(r=1,...,R)r^2=R(R+1)(2R+1)/6,

B_(D,R,n) <= [2pi^2/(3n^2)] (R+1)(2DR+1).             (4)

To verify the finite power-sum identity without a supplied formula, telescope (r+1)^3-r^3=3r^2+3r+1 and r(r+1)-(r-1)r=2r; summing gives the displayed expression. In (1), multiply by the nonnegative factor4(2DR+1)/(R(2R+1)) and cancel the positive integer R(2R+1). This yields (4) with no summation, dimension or quadrature loss. For finite R the linear/lower-order terms in (R+1)(2DR+1) MUST be retained; it is false to replace this by2DR^2 as an exact upper bound.

## 4. Full integer-side family and positive density

Fix alpha in(0,1/2), c>0 and m>=0 independent of n. Let R_n=floor(alpha n). For all sufficiently large positive integers n, R_n>=1 and 2R_n<n (indeed 2R_n<=2alpha n<n). Floor inequalities give R_n/n->alpha and (2R_n+1)/n->2alpha, hence H_n/n^D->(2alpha)^D.

Suppose the ORIGINAL local hypotheses in Section1 hold at each sufficiently large n with these SAME c,m. The maps C_n, derivatives L_n, targets F_n, signed weights, quadratic constants K_n, neighbourhoods delta_n and coercivity radii may depend arbitrarily on n, subject to their separate finite-side hypotheses. The finite theorem first handles each n. No limit of derivatives, common differentiability neighbourhood or uniform quadratic penalty bound is taken or needed.

From(2), A_(R_n)(pi/n)/R_n converges to

1/2 - sin(2pi alpha)/(4pi alpha).

Indeed R_n*pi/n->pi alpha, (R_n+1)*pi/n->pi alpha, and R_n*sin(pi/n)->pi alpha, using sin t/t->1. All limiting denominators are positive. Also R_n*[1/R_n+2(D-1)/(2R_n+1)]->D. Thus(1) gives

B_(D,R_n,n) -> B_D(alpha)
B_D(alpha)=2D[1 - sin(2pi alpha)/(2pi alpha)].         (5)

Apply(3), divide by n^D>0 and take liminf:

liminf_(n->infinity) q_n/n^D
 >= (2alpha)^D [1-(m/c) B_D(alpha)].                 (6)

A purely elementary quadratic version follows directly from(4):

liminf q_n/n^D >= (2alpha)^D
 [1 - (4pi^2 D m/(3c)) alpha^2].                     (7)

No sparse divisibility subsequence is needed: floor(alpha n) works on the full integer tail. This closes the analytic cutoff/cardinality/density transport from the actual finite endpoint. It does NOT mark any new Lean family theorem compiled.

As alpha->0, B_D(alpha)=(4pi^2 D/3)alpha^2+O(alpha^4), so for every fixed c>0 and finite m>=0 an alpha makes(6) strictly positive. For m=0, let alpha increase to1/2 in(6); liminf q_n/n^D>=1. For m>0, one explicit interior choice maximizing the polynomial right side of(7) is

alpha_* = sqrt(3c/[4pi^2 m(D+2)]),
provided alpha_*<1/2, equivalently 3c<pi^2 m(D+2).

At that choice the bound is

[2/(D+2)] [3c/(pi^2 m(D+2))]^(D/2) >0.               (8)

Differentiating (2alpha)^D(1-a alpha^2), a=4pi^2 Dm/(3c)>0, gives derivative 2^D alpha^(D-1)[D-a(D+2)alpha^2]; hence this is the unique interior maximum. If the condition fails, use any smaller admissible alpha or the boundary supremum; do not claim the interior formula is attained within the domain. It is the optimum of the polynomial ESTIMATE, not a sharp optimum over admissible observations, repair weights or packets, nor necessarily the optimum of exact(6).

The worst-coordinate bound would instead use B<=4pi^2 D(R/n)^2 and asymptotic coefficient4pi^2 D. Actual trace averaging gives4pi^2 D/3: a factor THREE smaller low-frequency quadratic coefficient. When both polynomial optimizers lie in(0,1/2), their resulting polynomial density guarantees differ by3^(D/2). This is a comparison of sufficient estimates, not improved physical gap or a new general spectral fact.

## 5. Verification, novelty and use

Exact sanity cases checked directly: R=1 yields B=4sin^2(pi/n)(2D+1)/3. For D=2,n=3, the three frequencies have lambda6,3,6, each with two quadratures, H=6, S=30 and B=5, matching(1). For D=2,n=4 the lambdas are4,2,4, H=6, S=20 and B=10/3. For D=3,n=3,R=1, first direction contributes3 and each other direction contributes2, B=7. These are hand-derived exact trig values, not numerical tests or Lean checks. The R=0 exclusion, m=0 case and c>0 division are explicit. Taking alpha->0 in(5) recovers the leading coefficient of(4); taking alpha->1/2 in(5) gives2D, providing another normalization check.

Primary context: Lin,Wan,Zhang, Connection Laplacian on discrete tori with converging property, arXiv:2403.06105 (submitted10March2024), Theorem1.2/its standard discrete-torus setting, https://arxiv.org/abs/2403.06105 . Discrete torus sin-squared spectra are established prior work. Gressman's original university lecture notes display the finite Dirichlet-kernel ratio and geometric-series proof, https://www2.math.upenn.edu/~gressman/analysis/08b-convergence.html ; search result accessible, direct fetch403, so no claim of full text inspection there. The independent telescoping proof in Section2 supplies the identity here without that source. Exact finite proof endpoint, packet definitions and prior in-repository coarse density arguments are separately attributed above. No claim of original priority for the combined consequence; a targeted source check does not establish novelty.

This belongs with the existing full-volume signed-mean manuscript, not a separate paper of small corollaries. Originality of elementary Fourier/trace tools is low; programme relevance is quantitative closure/improvement from the actual verified finite endpoint. Numerical finite bound, asymptotic density and optimized sufficient constant are analytic only until their exact Lean counterparts are compiled and reproduced. Publicv4 remains unchanged and its previous score is not transferred. No interacting-background producer or continuum construction follows. PR29 remains20/41;TermSource=0.
