# Signed weights require control of their positive spatial mean

The directional spatial mean obstruction extends to arbitrary signed repair
weights if the mean is taken after discarding their negative part. It does
not extend using the ordinary signed mean: all such means can be identically
zero while a fixed finite-dimensional linear observation and a nonnegative
quadratic penalty give uniform coercivity on the entire actual cochain
space. These statements delimit the nonnegative-weight hypothesis in the
existing coarse-information dossier.

## Actual finite lattice definitions

Fix integers d>=2, Nc>=2 and positive lattice side n. Write
X_n=(Z/nZ)^d, V_n=n^d and m=Nc^2-1. The actual real cochain space is
E_n={A:X_n x {1,...,d}->R^m}, with the counting Euclidean norm. Set

    (G_n A)_(k,x,l) = A_l(x+e_k)-A_l(x).

For actual scalar weights w_n(k,(x,l)), let R_w=G_n^* W_n G_n and

    Q_w(A) = <A,K_(0,n) A> + <A,R_w A>.

The repository's exact componentwise energy identity is

    <A,R_w A> = sum_(k,x,l) w_n(k,(x,l)) ||(G_n A)_(k,x,l)||^2.     (1)

It holds for arbitrary real weights. The actual flat Hodge identity is
<A,K_(0,n)A>=||G_n A||^2, so this Hodge term is nonnegative. There is no
hidden lattice-rescaling factor. Let D_n=ker(delta_n) be the actual flat
divergence-zero space.

For a fixed pair i!=j define the ordinary mean and positive-part mean by

    b_ij(n)   = V_n^(-1) sum_x w_n(i,(x,j)),
    b_ij^+(n) = V_n^(-1) sum_x max(w_n(i,(x,j)),0).

The superscript + means the mean of the pointwise positive part, NOT
max(b_ij(n),0). That distinction is essential below.

## Extension using the pointwise positive part

Retain the local nonlinear hypotheses of the mean-weight theorem: actual
finite-dimensional output F_n, C_n(0)=0, Frechet differentiability at zero,
positive local radii, a local penalty upper bound Phi_n(y)<=K_n||y||^2,
and one fixed c>0 such that

    c||A||^2 <= Q_(w_n)(A)+Phi_n(C_n(A))

for actual A in D_n in the stipulated local ball. No lower bound on w_n
is imposed. If (1+b_ij^+(n))/n^2 ->0 for one fixed transverse pair i!=j,
then dim_R F_n ->infinity.

Proof. Construct the actual weights w_n^+(p)=max(w_n(p),0). Their
nonnegativity is proved pointwise. Equation (1) gives, for every actual A,

    <A,(R_(w_n^+)-R_(w_n))A>
       = sum_p max(-w_n(p),0) ||(G_n A)_p||^2 >=0.                 (2)

Thus the original local coercivity inequality implies the same inequality
with the constructed w_n^+ and the identical C_n, Phi_n, c, local balls
and penalty constants. Apply the already proved actual nonnegative-weight
theorem to these explicitly constructed weights. Its actual directional
mean is exactly b_ij^+(n), by definition, and its quantitative conclusion is

    c(2R-dim F_n) <= 2(1+b_ij^+(n)) sum_(s=1..R)|exp(2*pi*i*s/n)-1|^2
                  <= 8*pi^2(1+b_ij^+(n))*R^3/n^2,    0<=R<n.     (3)

For each fixed R the last expression tends to zero. It is eventually
less than c. Integrality then forces dim F_n>=2R eventually; arbitrary
fixed R proves divergence. This is a proved domination step, not an
assumed positivity or trace certificate for the original signed operator.
In particular original Q_(w_n) need not be positive on the full space.
No bound on derivative norms, K_n or inverse neighborhood radii, uniform
in n, is introduced.

The statement removes global nonnegativity of the original weights, but
does NOT prove those original weights nonnegative. It replaces their
ordinary mean condition by the explicit positive-part mean condition.
On the original nonnegative class the two conditions are identical; for
signed weights the positive-part condition contains additional information.
It is also weaker than an absolute-mean condition, because max(w,0)<=|w|.

## Counterexample with every ordinary directional mean zero

For each n>=1 put a_n=2*d*n^2 and take zero as the distinguished site.
Define actual weights in EVERY direction/component pair by

    w_n(k,(x,l)) = a_n*(1 - V_n*1_(x=0)).                         (4)

All ordinary means vanish exactly:

    V_n^(-1) sum_x w_n(k,(x,l)) = a_n - a_n = 0.                  (5)

Consequently even the condition that ALL ordinary directional means divided
by n^2 tend to zero, or that ALL their positive parts max(b_kl(n),0) do,
holds. The same is true for the absolute value of each signed mean. These
conditions do not control the mean of the pointwise positive part.

Let mu_n(A)_l=V_n^(-1) sum_x A_l(x), and collect the actual gradient
values at the distinguished site:

    J_n(A)_(k,l) = A_l(e_k)-A_l(0).

Use the fixed output space

    F = (R^m)^d x (R^m)^(d*d),
    C_n(A)=(mu_n(A),J_n(A)).                                    (6)

Equip each factor and the product with the Euclidean sum norm. Each C_n
is an actual linear map on a finite real space, hence continuous and
smooth, vanishes at zero, and has derivative C_n itself. The real output
dimension is (d+d^2)*m, independent of n. No supplied low-rank factorization
or abstract observation certificate is used.

For (y,z) in F choose the nonnegative quadratic penalty

    Phi_n(y,z)=2*V_n*||y||^2+a_n*V_n*||z||^2.                    (7)

It is smooth, zero at zero, and obeys the global upper bound

    Phi_n(y,z) <= V_n*(2+a_n)*||(y,z)||^2.                       (8)

There is no weakened penalty regularity or nonquadratic growth here. The
bound K_n=V_n*(2+a_n) is finite for each n, as allowed in the theorem.

Expanding the ACTUAL repair energy (1) with (4), not just its trace, gives

    <A,R_(w_n)A> = a_n||G_n A||^2-a_n*V_n*||J_n(A)||^2.

Adding (7) at the actual observation (6) cancels the negative localized
part exactly. For every A in E_n,

    Q_(w_n)(A)+Phi_n(C_n(A))
      = <A,K_(0,n)A>+a_n||G_n A||^2+2*V_n*||mu_n(A)||^2
      >= ||A||^2.                                               (9)

The last inequality is the actual quadratic mean construction, proved in
the pinned source cited below. Here is also its elementary argument. If
M_n A is the constant lift of mu_n(A), then

    ||A-M_n A||^2 <= d*n^2||G_n A||^2,
    ||M_n A||^2 = V_n||mu_n(A)||^2.                              (10)

For the first estimate, Jensen bounds each squared difference from the
arithmetic mean by the average of squared pairwise differences. Connect
each ordered pair x,y by the coordinate-ordered forward path on the
periodic lattice. Its length is at most d*n. For a fixed oriented edge
in direction k, there are at most n^(d+1) ordered pairs whose canonical
path uses it: the other coordinates contribute n^(d-1) free choices and
the two endpoint coordinates in direction k contribute at most n^2.
Each such edge is used at most once on a given path. Pathwise
Cauchy--Schwarz, then summation over pairs and division by V_n, gives
d*n*n^(d+1)/V_n=d*n^2 times the total edge energy. Sum over cochain
components for the actual norm (10). The second estimate is direct
counting of the V_n copies of the constant mean. Finally

    ||A||^2 <= 2||A-M_n A||^2+2||M_n A||^2
              <= a_n||G_n A||^2+2*V_n||mu_n(A)||^2,

which proves (9), including n=1 (all forward differences then vanish).

Thus c=1 is a uniform GLOBAL coercivity constant, in particular on every
local ball in D_n, with smooth linear observations, a fixed output space,
and nonnegative exactly quadratic penalties. Yet all b_kl(n)=0. Removing
the weight nonnegativity hypothesis while retaining only ordinary signed
means makes the desired rank-divergence conclusion FALSE.

For n>1 the positive-part means of (4) are instead

    b_kl^+(n)=a_n*(1-1/V_n),
    b_kl^+(n)/n^2 -> 2*d.                                       (11)

The positive-part extension (3) therefore does not apply to this
counterexample. There is no contradiction between the two results.

## Where the positivity proof fails

The issue is visible even on the actual divergence-free space. Fix i!=j
and an internal unit vector u. For n>=3 take the cochain with only
component j nonzero and

    A_j(x)=u*1_(x_i=0).

It is independent of x_j, hence has zero actual divergence. There are
exactly 2*n^(d-1) nonzero forward differences, all in direction i, each
with squared norm1. At the distinguished site the sum of their squared
norms is1. Therefore (1), (4) and the Hodge identity give

    Q_(w_n)(A)=2*n^(d-1)*(1+a_n)-a_n*V_n
              =n^(d-1)*(2-a_n*(n-2)) <0.                        (12)

The strict sign follows from d>=2, n>=3 and a_n=2*d*n^2. Hence the
positive complementary-trace argument cannot be applied to these original
signed operators, even after restricting to divergence zero. Local
coercivity is restored by the genuinely observed fixed collection J_n,
not by an implicit positivity premise. Replacing w by w^+ in (2) is a
different, explicitly proved upward comparison that avoids this failure.

## Verification and relation to the existing manuscript

These are complete analytic proofs. The new signed-weight construction
and positive-part family composition have NOT been checked by Lean in
this unit, and no independent scientific review or original-priority
claim is made. The actual identities and mean-coercivity baseline used
in the proof have existing separately tested formal sources:

- ComponentwiseFlatGradient.lean, componentwiseWeightedRepair_energy:
  exact real-weight energy formula (1), with no sign assumption.
- ComponentwiseFlatHodge.lean: actual whole-space gradient/Hodge identity.
- PhysicalQuadraticMeanRepair.lean, physicalQuadraticMean_global_coercive:
  tested source7f37d6437a8f69a1d3fddf3dc0bcfad74c6bf9b6, two matching own
  fresh Colab clones067/067b, supplies the actual baseline in (9)--(10).
- PhysicalAverageWeightFamily.lean: tested
  sourceac60c0df885d8866329a839e2b4e73c90595d806, two matching own fresh
  Colab clones076/076b, supplies the nonnegative theorem used after the
  explicit construction and comparison (2).

The classical background is the weighted-Laplacian quadratic-form
identity and finite-dimensional observation of a localized finite-rank
negative contribution. Spielman's author-hosted Graphs, Vectors, and
Matrices, Section2, states the weighted energy formula for positive
weights; it is primary background for the algebra, not a source asserting
our signed counterexample or a novelty certificate:
https://cs-www.cs.yale.edu/homes/spielman/PAPERS/bull1557.pdf
The author-hosted source was consulted on2026-10-31 after an initial direct
lookup timed out. No exhaustive priority search has been completed.

This result belongs to the same coarse-information dossier. The exact
15-page v4 PDF e5e9ddcf044ddcfab0e4cae8e2c6ac1a3dca39ff21bf23b20989aaff4b220e05
and its already received author permission remain unchanged: this research
note is NOT contained in that frozen PDF and creates no separate paper,
deposit, model assessment or public license permission for another PDF.
PR29 remains20/41;TermSource=0. No interacting/continuum hypothesis,
physical mass gap or volume-density theorem is obtained.

## Single question and falsifiers

Question: can signed weights replace nonnegative weights under the same
ordinary directional-mean hypothesis, and what explicit mean condition
still gives the actual rank obstruction?

Answer: ordinary signed means fail by (4)--(9), even when every such mean
is zero. Pointwise positive-part means suffice by the derived comparison
(2)--(3). No additional question is opened here.

Falsifiers checked in the proof: wrong counting norm or forward shift;
mistaking max(mean(w),0) for mean(max(w,0)); incorrect sign of the localized
correction; varying output dimension; loss of local quadratic penalty;
hidden uniform-neighborhood requirement; and applying original-operator
positivity despite the explicit divergence-free negative field (12).
The finite n=1 case, negative-field range n>=3, and fixed d,Nc are stated
separately. A formal implementation must construct the actual positive
part and prove its energy comparison rather than assume them as fields.
If that implementation makes no substantive progress for three units,
retain this analytic result and identify the precise API or proof blocker.
