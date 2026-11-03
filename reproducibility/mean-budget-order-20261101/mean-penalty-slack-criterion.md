# Kernel slack: exactly when a finite larger mean penalty exists

3 November 2026, unit109. Supplement to interblock-shorted-energy.md at
66119388974724caa72cab93587dcf1d2d59d33c. This treats freely chosen finite
K, which the original nonlinear observation class permits. It does NOT
replace the fixed-K=c rectangular strengthening by an easier question.
No endpoint rank theorem, new hypothesis elimination or separate paper.

## 1. Necessary and sufficient finite-dimensional condition

Use the same finite real spaces, L>=0, normalized means C, orthogonal
P=C*C and Q=I-P, and blocks A=PLP, B=PLQ, D=QLQ. Fix c>0 and put
J=D-c I on N=ker C. There exists a finite K>=0 such that

    <u,Lu> + K||Cu||^2 >= c||u||^2 for every u              (1)

if and only if

    J>=0 and Bv=0 for every v in ker J.                    (2)

Necessity: set u=v in N to get J>=0. For v in ker J and p in ran P,
the quadratic form in u=v+t p has zero constant term. Nonnegativity for
both signs of t forces its linear coefficient 2<p,Bv> to vanish. Hence
Bv=0; finite K cannot repair a nonzero linear cross term at equality.

For sufficiency, ker J subset ker B implies ran B* subset ran J. The
finite spectral pseudoinverse J^dagger is therefore applicable to B*p.
With u=p+v, direct completion gives

    <u,Lu>+K||Cu||^2-c||u||^2
      = <v+J^dagger B*p,J(v+J^dagger B*p)>
        + <p,[A+(K-c)I-B J^dagger B*]p>.                  (3)

Since A>=0, the explicit finite choice

    K=c+||B J^dagger B*||                                (4)

suffices. This proves existence without assuming invertibility of J or A.
If N is zero, take J^dagger=0 and K=c; the same formulas apply. Neither
(2) nor (4) assumes the desired inequality as a structure.

## 2. A strict kernel margin gives an explicit actual-coefficient penalty

If for some epsilon>0 the PROVED kernel estimate is D>=(c+epsilon)I,
then J>=epsilon I and (2) holds automatically. Also ||B||<=||L||, so

    K=c+||L||^2/epsilon                                 (5)

is a safe actual penalty. No lower bound for A or the quotient graph gap
is needed. This is useful because the number of mean outputs is unchanged.
It does not prove the kernel estimate or construct/count a partition.

For the actual scalar-start finite torus stiffness

    E_a(u)=sum_(x,i) a(x)|u(x+e_i)-u(x)|^2,
    1<=a(x)<=2m,

each vertex has at most2D incident oriented forward-edge occurrences,
each weight at most2m. Using |r-s|^2<=2|r|^2+2|s|^2 directly gives

    E_a(u)<=8Dm ||u||^2, hence ||L_a||<=8Dm.              (6)

For n=2 the parallel directed occurrences are both counted; the bound
still holds. Loops at n=1 have zero difference. Repeated field/internal
components are orthogonal direct sums, so there is no factor h in(6).
Consequently a proved all-cochain kernel margin2c would supply

    K=c+64D^2 m^2/c.                                    (7)

The original data then are the ACTUAL linear C, Phi(y)=K||y||^2, C(0)=0,
with any positive neighbourhood radii. These data hold on divergence-zero
fields as a restriction. No requirement in that original class makes K
uniform in n,m or the profile. For that class one need not additionally
prove the unit108 fixed-penalty shorted bound S>=cI once strict kernel
slack is established. The stronger normalized-map requirement K=c still
requires that bound. These two goals must remain distinct.

If one proves a kernel estimate only within the divergence-zero space,
the decomposition p+v used above is NOT automatically available there:
ordinary rectangular averaging need not preserve divergence. Equations
(5)-(7) use an all-cochain kernel estimate; no restricted physical estimate
is silently substituted. A separate restricted-space analysis would be
needed to remove that qualification.

## 3. Exact equality obstruction: kernel bound alone can fail for EVERY K

Use the same four-cycle with edge weights(1,6,4,1), two blocks{0,1},{2,3},
and kernel v=(x,-x,y,-y). Its energy is

    E(v)=11x^2+14xy+23y^2, ||v||^2=2(x^2+y^2).

Put s=sqrt(85) and c_star=(17-s)/2>0. Then

    E(v)-c_star||v||^2
      =(s-6)x^2+14xy+(s+6)y^2
      =(s-6)[x+7y/(s-6)]^2 >=0,                         (8)

because (s-6)(s+6)=49 and s>6. Equality holds at x=7,y=6-s.
For that nonzero v, r=x+y=13-s>0. Add block constants
p=(delta/2,delta/2,-delta/2,-delta/2). Crossing-edge energy is
6(delta-r)^2+(delta+r)^2, and the internal energy is unchanged.
As p is orthogonal to v, ||p||^2=||Cp||^2=delta^2. Thus the exact defect
of(1) at u=v+p and c=c_star is

    (7+K-c_star)delta^2-10r delta.                        (9)

For EVERY finite K>=0, 7+K-c_star>0 (since c_star<7). Choose
0<delta<10r/(7+K-c_star); (9) is negative. Therefore kernel coercivity
at equality is insufficient even when the penalty coefficient is free.
This is a finite exact symbolic example, not an executable experiment.

Weights still have minimum1, mean3, maximum6=2m. The counterexample is
to a general finite-cycle inference. It is NOT a claim that the entire
D-dimensional physical kernel satisfies c_star, nor a falsifier defeating
every rectangular partition. Unit108's prescribed fixed-size lattice
witness and its qualifications remain unchanged.

## 4. Context, verification and next step

The mathematical mechanism is classical positive-block completion/Schur
complement, not new operator theory. Primary related sources:
Anderson and Trapp, Shorted Operators.II, SIAM J.Appl.Math.28(1),60-71,
1975, DOI10.1137/0128007 (publisher abstract/metadata checked in108);
Dorfler and Bullo, Kron Reduction of Graphs with Applications to Electrical
Networks, https://arxiv.org/abs/1102.2950 (primary author abstract checked
in109). The latter concerns node elimination; it is context, not a theorem
asserted to be identical to mean-subspace elimination. Our finite criterion
and constants are derived explicitly above. Full priority is not verified.

Analytic audit: both signs in the necessity polynomial; singular range
condition; orientation B:N->M and BJ^daggerB*; nonnegative explicitK;
N=0; norm8Dm with parallel edge counting; absence of an h factor; freeK
versus fixedK; non-preservation of divergence by P; exact discriminant85;
product49 in(8); r>0; all finiteK sign/choice in(9).

No new numeric model assessment was requested for this supplement; the
previous exact note's first4/10 belongs only to its immutable66119388
source, not to this new material. Same preparing Codex agent, backend and
effort unexposed, analytic self-audit only. No independent or human review,
Lean proof, executed arithmetic, fresh clone or physical/continuum claim.
Limitations retained: classical mechanism; kernel bound/count unresolved;
margin essential unless coupling vanishes on equality; all-cochain
requirement for(7); possible largeK; cycle-only kernel-pass example; no
all-partition/asymptotic falsifier or originality certificate.

ONE active critical rectangular question remains. Next determine whether
a target-count actual rectangle construction proves kernel margin2c; if
so(7) closes its ORIGINAL free-penalty obligation without another coupling
assumption. For the fixedK=c strengthening retain the unit108 shorted
criterion and do not claim a solution by enlarging K. This is mechanism
unit2 without global endpoint advance; old mass-only route counter3 stays.
After a third unit without such advance, change route or name the exact
remaining blocker. No new paper/PDF/AIRR submission; PR29=20/41,TermSource=0.
