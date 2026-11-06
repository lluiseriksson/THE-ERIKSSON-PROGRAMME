# Sharp compensation of negative diagonal-gradient channels on the actual flat cochain domain

Supporting result155 for the existing Hodge/coarse-information dossier. This is not a new standalone paper and does not alter the frozen reviewed PDF ccf53e0afc9819c3fc9b2008de9076a60f60d23ef6ac2c4ccd82adca30cbf389 or its7.6AI score. Mathematical proof below is analytic, not Lean verified. Classical discrete Korn/Hodge and Fourier methods; no claim of a new general principle or established priority.

## Actual objects and the closed bounded question

Let D>=2,n>=2,m>=1, X=(Z/nZ)^D, N=n^D. In the programme take D>=3 and m=Nc^2-1. An actual real cochain is A:X->{R^m}^D with counting norm. Write D_i^+f(x)=f(x+e_i)-f(x), D_i^-f(x)=f(x)-f(x-e_i), and delta A=sum_i D_i^- A_i. All shifts are periodic, including n=2 parallel occurrences. Set

T(A)=sum_(x,i,j) |D_i^+ A_j(x)|^2,
L(A)=sum_(x,i) |D_i^+ A_i(x)|^2,
O(A)=sum_(x,i!=j) |D_i^+ A_j(x)|^2,
V(A)=sum_x |delta A(x)|^2,
S(A)=sum_(x,i<j) |D_i^+ A_j(x)+D_j^+ A_i(x)|^2.

Here O is off-diagonal derivative energy, NOT the observation norm. Denote that norm by B(A)=N*sum_j|mean_X A_j|^2. The actual normalized global mean C has coordinates N^(-1/2)*sum_x A_j(x), hence B=|CA|^2 and dim F=Dm. Write P(A)=|A-mean_X A|^2, so |A|^2=P+B.

Fix a>0 and kappa>=0. Actual scalar coefficients alpha_(i,j,r)(x) may depend arbitrarily on x, derivative direction, field component and internal coordinate; assume ONLY

alpha_(i,j,r)(x)>=a if i!=j,
alpha_(i,i,r)(x)>=-kappa if i=j.

No common profile, upper bound, inverse-moment bound or positivity of diagonal coefficients is assumed. Define the actual form
Q_alpha(A)=sum_(x,i,j,r) alpha_(i,j,r)(x)*(D_i^+ A_(j,r)(x))^2.

It equals the original flat Hodge form H0 plus the actual gradient repair G*W G with W_(i,j,r)(x)=alpha_(i,j,r)(x)-1: periodic unweighted curl/divergence cancellation gives H0=T. We do not assert a weighted curl-divergence cancellation.

Closed question155: under these literal channel bounds, what are the SHARP uniform conditions for a given c>0 and K to obtain Q_alpha+K*B>=c*|A|^2 on delta A=0? Can a divergence penalty beta*V produce an equally sharp full-space characterization? Mechanism: unweighted mixed-square identity plus an explicit Fourier support split; compare variable coefficients with constants before applying either. Falsifier: a profile and actual cochain violating the proposed bound, or a failure of the mixed identity at n=2. Abandon this mechanism if it requires moving variable coefficients through summation by parts or assumes the desired physical coercivity in a structure. The question is settled below in this unit; it is not a second ongoing research question.

## Lemma1: exact mixed-square identity, with proof

On ALL actual cochains,

S=O+V-L.                                                    (1)

For i!=j, periodic adjointness and commuting shifts give
sum_x <D_i^+ A_j,D_j^+ A_i>=sum_x <D_j^- A_j,D_i^- A_i>.
Indeed (D_i^+)*=-D_i^- and (D_j^-)*=-D_j^+, and the shifts commute. Also |D_i^+ A_i|^2=|D_i^- A_i|^2 by translation. Expanding each square in S and V proves(1), with unordered pairs counted once. In particular L<=O on delta A=0. This is proved, not supplied as a comparison certificate.

## Lemma2: sharp off-diagonal-plus-divergence Poincare bound

With lambda_n=4*sin(pi/n)^2,

O(A)+V(A)>=lambda_n*P(A)                                   (2)

for every actual cochain. To prove it, complexify the finite counting-unitary Fourier expansion (apply to each real internal coordinate and use conjugate pairs, without doubling real dimensions). At frequency k let z_i=exp(2*pi*i*k_i/n)-1, s_i=|z_i|^2, and s=sum_i s_i. A nonzero s_i is at least lambda_n. The off-diagonal energy of its field amplitude u is sum_j(s-s_j)|u_j|^2; divergence energy is |sum_j(1-exp(-2*pi*i*k_j/n))*u_j|^2.

If exactly one s_t is nonzero, these two terms sum to s_t*|u|^2: O supplies all components except t and V supplies component t. If at least two s_i are nonzero, every s-s_j>=lambda_n, so O alone is at least lambda_n*|u|^2. The zero frequency contributes neither energy nor P. Summing the finite Parseval identities gives(2). Equality occurs for a single-frequency field; the constant is sharp. This proof includes n=2.

## Theorem: exact uniform physical and full-space conditions

All universal quantifiers below range over the complete coefficient family obeying the displayed pointwise bounds. They are NOT necessary conditions for an individual profile when its chosen lower bounds are loose.

(A) For c>0,

forall alpha, forall A with delta A=0:
 Q_alpha(A)+K*B(A)>=c*|A|^2

holds IF AND ONLY IF

K>=c and (a-kappa)*lambda_n>=c.                             (3)

(B) For a real beta and c>0,

forall alpha, forall actual A:
 Q_alpha(A)+beta*V(A)+K*B(A)>=c*|A|^2

holds IF AND ONLY IF

K>=c, (a-kappa)*lambda_n>=c, (beta-kappa)*lambda_n>=c.        (4)

Proof of sufficiency. First compare coefficients pointwise, without integration by parts through alpha:
Q_alpha>=a*O-kappa*L.
Using(1), on all fields

Q_alpha+beta*V>=kappa*S+(a-kappa)*O+(beta-kappa)*V.           (5)

Under(4), put g=c/lambda_n>0. Both O,V coefficients in(5) are at least g, while kappa*S>=0. Lemma2 gives Q_alpha+beta*V>=c*P. Add K*B>=c*B. For(A), choose beta=a in this already-derived full-field implication; on the actual physical domain V=0 identically, proving(3) without any assumed kernel-coercivity field.

Sharp necessity, actual real fields. Let T0 be a fixed unit internal vector and f(t)=cos(2*pi*t/n). It has counting mean zero for every n>=2 and its squared difference sum is lambda_n times its squared norm. Take the constant allowed profile alpha^0 with off-diagonal coefficients a and diagonal coefficients -kappa.

(i) Constants A_1=T0 force K>=c, since Q=V=P=0 and B=|A|^2>0.
(ii) Take A_1(x)=f(x_1+x_2)*T0, A_2(x)=-f(x_1+x_2)*T0, other components zero. Its backward divergence is exactly zero because the two backward differences coincide and cancel. B=0, L=O=lambda_n*|A|^2, S=0. Thus Q_alpha0=(a-kappa)*lambda_n*|A|^2. This forces the second inequality in both(3),(4).
(iii) For(B), take A_1(x)=f(x_1)*T0, others zero. Then O=B=S=0, L=V=lambda_n*|A|^2, so Q_alpha0+beta*V=(beta-kappa)*lambda_n*|A|^2. This forces the third inequality in(4). Each is a literal actual-domain witness, not an arbitrary matrix surrogate. This proves both iff statements.

## Eliminated assumption and sharp failures

Uniform positivity of ALL derivative coefficients is unnecessary for this explicitly bounded family. Diagonal coefficients can vanish (kappa=0) or be negative (0<kappa<a). Even coefficients depending arbitrarily on x/components are covered. The physical coercivity premise is derived by(1),(2),(5), not moved to data fields. The all-field operator may be indefinite: for kappa>0, witness(iii) has Q_alpha0=-kappa*lambda_n*|A|^2<0 even while(3) gives positive physical coercivity. Confusing those domains would be a substantive error.

The compensation threshold is sharp. At kappa=a, the nonconstant divergence-zero witness(ii) has zero energy and zero global mean; no finite mean penalty can yield c>0. For kappa>a it has negative energy. Thus positivity of the average channel coefficient cannot replace the directional condition: for D>=3 and kappa=a, the baseline channel average is a*(D-2)/D>0, but the actual physical null field remains. This negative result is exact, not a numerical sample.

For a family over n with common c>0 and finite-output normalized global means, the uniform class guarantee requires and suffices that K_n>=c and a_n-kappa_n>=c/lambda_n for every n under consideration. Since lambda_n~4*pi^2/n^2, the necessary growth is quadratic. This is a finite unit-spacing cochain statement, not an interacting or continuum Yang-Mills spectral-gap result. No unrestricted critical rectangular partition theorem or moment hypothesis is proved. Generic common-refinement remains STOPPED3; the original single active rectangular question is unchanged.

## Attribution and verification limits

The mechanism is classical finite Fourier/Poincare and Korn/Hodge square algebra. No new general spectral or elasticity principle is claimed. A bounded primary-source check found Gopalakrishnan,Kogler,Lederer,Schoeberl,arXiv:2112.00089v4, whose abstract describes exactly divergence-free finite elements and Korn-like stability with the symmetric gradient. Its discretization is different; neither its theorem nor the present sharp signed-channel constants are identified as the same result on that basis. The abstract/metadata and the HTML Korn-stability discussion were inspected; no equivalence of discretizations or constants is inferred. Publisher search results for Pichugin/Prikazchikov's explicit strong ellipticity conditions in incompressible solids, QJMAM69(2016),67ff, give related constrained-ellipticity context, but full publisher access failed and no precise theorem is imported. An author-hosted Chen/Wang PDF lookup also failed. This is not an exhaustive priority check or evidence of novelty.

Primary source: https://arxiv.org/abs/2112.00089v4
Context lookup: https://academic.oup.com/qjmam/article/69/1/67/2948297

A separate exact finite diagnostic checks literal polynomial coefficients of(1) and actual real witnesses on small tori. Those checks are diagnostics of this analytic proof, not Lean verification, independent authorship, exhaustive literature review or a new model assessment. Keep their real status and failures separate. The already-reviewed publication candidate and its pending author grant remain untouched.