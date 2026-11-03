# Critical local moment bounds require a geometric factor

Unit106, 3 November2026. Existing mean-budget dossier, not a separate paper. Base delivery head6e90f7078962044e6dd0a72125a6560c1b4ac7b2. This is an analytic rectangle adapter and a useful counterexample to a proposed LOCAL certificate. It does not settle the unrestricted rectangular-partition question. No new Lean execution, numerical experiment, independent review, PDF or AIRR action is claimed.

## Exact statement

Let D>=3, p=D/2 and q=2D/(D+2). For an integer rectangle

    R=product_i {0,...,l_i-1}, V=product_i l_i, L=max_i l_i,
    kappa(R)=L^2/V^(2/D),

let E(R) contain each internal positive-axis edge once. For arbitrary positive edge coefficients b_e, put

    E_b(u)=sum_e b_e |du(e)|^2,
    mu_e(R)=sum_e b_e^(-p),
    Var_R(u)=sum_R |u-mean_R u|^2.

There is a finite constant A_D depending only on D such that

    Var_R(u) <= A_D*kappa(R)*mu_e(R)^(1/p)*E_b(u).       (1)

This includes sides of length1. If V=1, both residual and edge energy are zero and the conclusion is immediate. For the actual scalar-start profile b_(x,x+e_i)=a(x), set mu_v=sum_R a(x)^(-p). Since mu_e<=D*mu_v,

    Var_R(u) <= A_D*D^(2/D)*kappa(R)*mu_v^(2/D)*E_a,R(u). (2)

The same assertion holds coordinatewise for the actual flat field, with no extra coefficient-space dimension in the inequality. Edges are internal edges of R; no weights are reassigned and no enlarged-region energy is assumed.

The factor kappa cannot be replaced by a D-dependent constant in (2). More precisely, for EVERY rectangle with L>=2 and uniform a>0, its optimal local Poincare constant P(R,a) satisfies

    P(R,a) >= L*(L+1)/(12*a)
            >= (1/12)*kappa(R)*mu_v(R)^(2/D).            (3)

Together (2),(3) show the necessary geometric dependence, up to D-dependent constants, even in the uniform subclass. They do not say that this factor is optimal for each heterogeneous profile.

## 1. Balanced-cube input, with its actual normalization

On an odd axis cube Q of side s>=3, the counting-norm endpoint Sobolev inequality is

    Var_Q(v) <= C_D*(sum_internal_axis_edges |dv|^q)^(2/q). (4)

This is an external classical analytic input with explicit graph adapters, not an added unproved coefficient hypothesis. Primary source: Andres, Deuschel and Slowik, arXiv:1312.5473v6, Section2.2, equation(2.5); rechecked on3November2026 at https://arxiv.org/pdf/1312.5473 . For alpha=q its target exponent D*q/(D-q) equals2. Their normalized radius factor, converted to counting norms, is bounded by a D-dependent constant because s^2*(s^D)^(1-2/q)=1. Directed/undirected edge factors are absorbed in C_D. Remark2.2 gives the same-ball form.

For completeness, the lattice-ball adapters are those proved in the dossier's higher-inverse-moment-adaptive-upper.md at6dcb893155e52f17d99921f5247dfefc83fe9e32, Section1, evaluated at the permitted endpoint q. Use the king graph so its balls are odd cubes. Canonical axis paths give sum_Q|v-mean v| <= (s/2)sum_axis|dv|. Applied to an indicator of at most half the cube, this gives at least2|A|/s crossing axis edges. Each internal boundary vertex accounts for at most2D such edges, verifying the source's relative VERTEX-boundary assumption with a D-dependent constant. Cube volume supplies volume regularity. Each king edge has an axis path of at mostD steps inside Q; finite D-dependent congestion transfers its q-gradient to internal axis edges. Thus all source assumptions and the actual edge/norm conversion for (4) are accounted for. No weighted, anisotropic, or interacting theorem is imported from that source.

## 2. Reflection proof for arbitrary aspect ratio

Assume L>=2. Choose the odd s=2L+1 and extend u to Q={0,...,s-1}^D by the endpoint-repeating coordinate folds of period2*l_i:

    0,1,...,l_i-1,l_i-1,...,1,0,0,1,... .

For l_i=1 the extension is constant in that coordinate. Write r=s^D/V. In a full period every original vertex has exactly two preimages. Since s/(2*l_i)>=1, floor(s/(2*l_i))>=s/(4*l_i); hence every vertex of R has at least

    product_i s/(2*l_i) = 2^(-D)*r

preimages in Q. An original coordinate vertex has at most s/l_i+2 <=3s/l_i preimages. The same bound holds for an internal undirected edge in its own coordinate; transverse coordinates use the vertex bound. Adjacent folded coordinates are either equal or form an original internal edge, in either orientation. Consequently each original internal edge has at most3^D*r preimages and

    sum_edges(Q) |d extended(u)|^q <= 3^D*r*sum_edges(R)|du|^q. (5)

No reflected weight assignment is made: (5) is an unweighted gradient statement. Let z be the counting mean of the extension on Q. Minimality of the original counting mean gives

    Var_Q(extended(u)) >= 2^(-D)*r*sum_R|u-z|^2
                       >= 2^(-D)*r*Var_R(u).            (6)

Apply (4),(5),(6). Since 2/q-1=2/D and s<=3L,

    Var_R(u) <= C_D*2^D*3^(2D/q)*r^(2/D)
                         *(sum_edges(R)|du|^q)^(2/q)
              <= A_D*kappa(R)*(sum_edges(R)|du|^q)^(2/q), (7)

where A_D=C_D*2^D*3^(2D/q+2) is one safe choice. The possibly large reflection multiplicities are included explicitly; treating them as a constant independent of aspect ratio would be incorrect.

Finally q/(2-q)=p and weighted Holder on ORIGINAL edges yields

    (sum_edges(R)|du|^q)^(2/q)
        <= E_b(u)*(sum_edges(R)b_e^(-p))^(1/p).         (8)

This proves (1) and then (2). No local Poincare certificate has been introduced as an assumption.

## 3. Exact counterexample to dropping geometry

Choose a coordinate of length L and set u(x)=x_1-(L-1)/2, independent of all other coordinates. Direct finite-sum identities give

    mean_R u=0,
    Var_R(u)=V*(L^2-1)/12,
    E_a,R(u)=a*V*(L-1)/L.

Their ratio is L*(L+1)/(12*a). For uniform a, mu_v=V/a^p and therefore kappa*mu_v^(1/p)=L^2/a. This proves (3) without an asymptotic or numerical calculation.

In particular choose R_L={0,...,L-1} times D-1 singleton coordinates and a=L^(2/D), L>=2. Then a>=1, its block arithmetic mean is m=a and a<=2m, while

    mu_v=1,
    mu_e=(L-1)/L <1,
    P(R_L,a) >= L*(L+1)/(12*L^(2/D)) -> infinity.

For any prescribed local coercivity constant c>0, sufficiently large L makes c*Var_R(u)>E_a,R(u). Thus neither uniformly bounded nor sufficiently small positive critical inverse mass alone supplies a uniform local certificate on arbitrary rectangles: for any fixed tau>0 take a=(L/tau)^(2/D), so mu_v=tau and the same ratio still diverges. All formulas are exact; no floating point or executable computation was used.

This local scalar test is NOT a counterexample to the original global divergence-zero observation inequality. It does not force an arbitrary partition algorithm to choose a thin rectangle, and omitted inter-block edges could control the field. It disproves only the proposed dimension-only, inverse-mass-only LOCAL block estimate. No global coefficient family or original nonlinear rank obstruction is asserted here.

## 4. Consequence for the active mechanism

For a sufficient local mean-block certificate at the critical exponent, (2) requires

    c*A_D*D^(2/D)*L(R)^2/V(R)^(2/D)
                              *mu_v(R)^(2/D) <=1.     (9)

Equivalently mu_v(R)<=V(R)/[L(R)^D*(c*A_D*D^(2/D))^(D/2)]. The right side is proportional to the volume fraction V/L^D, not a shape-independent mass threshold. Uniform coefficients already force that scaling, up to constants, by (3).

The proposed shortcut was to compress a unary chain of a full cube tree into a few anisotropic rectangles and reuse the critical cube mass test. Reflection shows the missing factor explicitly; the thin-rectangle example proves it cannot simply be removed. Combinatorial compression alone does not prove the endpoint result. It has not been shown that every such compressed shell actually violates coercivity, so that stronger assertion is not made.

Conservative progress audit: units104,105and106 have not resolved the GLOBAL critical rectangular target or proved a uniform partition-count reduction. Count this as the third unit without that substantial endpoint advance, despite the useful local adapter and refutation above. Concrete blocker identified: independent local certificates pay kappa(R), whose sum/count is uncontrolled by critical inverse mass under anisotropic compression. Stop that mass-only independent-block mechanism. Keep ONE active mathematical question, but switch its next mechanism to retaining inter-block energy in a global normalized-mean kernel estimate. If that cannot produce a proved reduction, record the obstruction rather than another local corollary.

The active statement remains: fixed D>=3,c>0,Nc>=2,M; actual scalar1<=a<=2m,mean a=m,mean((m/a)^(D/2))<=M; find an unrestricted rectangular normalized-mean partition with the original target rank and coercivity, or a falsifier defeating EVERY such partition. The present counterexample defeats a LOCAL proof criterion only. A candidate using global coupling must state its operator, zero-mean kernel estimate and actual rank count; assuming that estimate as a structure is not hypothesis elimination.

## Model assessments and review context

FIRST exact-note self-assessment5/10, same preparing Codex agent; served backend identity and effort unexposed. Rubric0-10: analytic derivation7, originality2, finite-dossier relevance6, formal/general verification maturity3. Overall5 is qualitative, not an average/probability. New source, no inherited grade and no repeated review to improve a score. No independent model review, human peer review, editorial acceptance or publication.

Audit: endpoint q and conjugate exponent; source relative vertex boundary; counting-norm conversion on odd cubes; exact endpoint-repeating fold; lower vertex and upper undirected-edge multiplicity; variance comparison about the extended mean; r exponent2/q-1=2/D; s<=3L; weighted Holder on original edges without reassigning scalar-start weights; dimension factor D^(2/D); linear-coordinate exact variance/energy; fixed-small-mass scaling; singleton and collapsed-side cases; local/global and scalar/divergence-zero distinctions; honest no-progress count and changed mechanism.

O1. New adapters are analytic, not Lean-verified; (4) uses the cited classical primary theorem and explicit existing graph adapters.

O2. The geometric factor and reflection/Sobolev method are classical in character. The source search establishes relevant prior mathematics, not originality or independence. No separate paper is warranted.

O3. The counterexample concerns a prescribed local block inequality, not every partition, original global nonlinear rank, or a physical model.

O4. The upper estimate can be loose on heterogeneous profiles. Sharpness is geometric uniform-coefficient dependence up to D-dependent constants, not an optimal profile-dependent formula.

O5. No executable diagnostics, fresh clones, oracle or numerical certificate were run. Verification is the displayed analytic derivation and exact finite-sum identities.

O6. Compressed-tree combinatorics and a global inter-block kernel estimate remain unproved. This note does not solve the sole active endpoint question or reset its no-progress counter.

O7. No new PDF, license inheritance, AIRR/ai.viXra deposit, acceptance or publication. Prior exact PDF36c4... first6/10 remains unchanged. PR29 remains20/41,TermSource=0; interacting/continuum physical gap remains open.
