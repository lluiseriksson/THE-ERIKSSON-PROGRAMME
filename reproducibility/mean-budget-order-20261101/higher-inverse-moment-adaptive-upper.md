# Higher inverse moments give actual adaptive block observations

Unit101, 2026-11-02. Base main cb3ad75970bfa921d8ad36830f91bb6214d9aa18. This analytic theorem closes the one active higher-inverse-moment question left by unit100. It belongs to the existing mean-budget dossier, not a separate paper. The new adapters below have NOT been Lean-compiled or independently reviewed. No numerical experiment or terminal reproduction is claimed.

## Statement and actual objects

Fix an integer D>=3, Nc>=2, c>0, a finite real p>D/2, and M>0. On the discrete torus (Z/nZ)^D, n>=1, let m>=1 and actual scalar total coefficients a(x)>0 obey

    n^(-D) sum_x (m/a(x))^p <= M.                         (H)

Use this same a(x)=1+w_(i,x,j) for every derivative direction i and field component j, with the actual forward gradient start x. The finite flat componentwise energy is

    E_a(U)=sum_(x,i,j) a(x)||U_j(x+e_i)-U_j(x)||^2.

The existing actual flat Hodge identity identifies E_a with Q_w in the dossier (formal source dfd49d0b0730a4d36f58a4cbb7a17d6a41fb60bc). We use precisely that scalar subclass and its actual counting norm. No analogous statement for interacting curvature is asserted.

There are a partition into N integer rectangles, an ordinary Euclidean space F of dimension h*N, h=D*(Nc^2-1), and the explicit linear observation

    C(U)_(B,j)=sqrt(|B|)*mean_B U_j,

such that, for EVERY actual cochain U,

    c||U||^2 <= Q_w(U)+c||C(U)||^2,
    dim F <= C_*(D,c,Nc,p,M)*max(1,(n/sqrt(1+m))^D).        (T)

Thus the original nonlinear local data are supplied by this C, Phi(y)=c||y||^2, K=c and any positive neighbourhood radii. The inequality in particular holds on actual divergence-zero fields. The partition depends on the coefficients; its bound does not. Neither a pointwise relative lower bound nor an abstract Poincare/rank certificate is an input.

The original question additionally imposed 1<=a<=2m and mean(a)=m. They are compatible with this implication but are not used in its proof. They have NOT been derived from other assumptions. In particular (H) is still an additional, substantive coefficient-distribution hypothesis, not a consequence of an arithmetic mean.

## 1. A proved local box inequality

We first justify, rather than assume, a constant kappa=kappa(D,p)>=1 such that every rectangle B with integer side lengths between ell/2 and ell, ell>=2, satisfies

    sum_B |u-mean_B u|^2
      <= kappa*ell^2*|B|*(|B|^(-1) sum_internal_axis_edges |du|^q)^(2/q),
    q=2p/(p+1).                                          (1)

Here 1<q<2<D, and q>D*2/(D+2), so q*=D*q/(D-q)>2. The edge sum in (1) is on B itself, without an enlarged box. For ell=1 the residual is zero.

The primary analytic input is Andres, Deuschel and Slowik, arXiv:1312.5473v6, section2.2, equation(2.5), printed page12, inspected directly at https://arxiv.org/pdf/1312.5473 . It gives a normalized local Sobolev inequality under their Assumption1.1; Remark2.2 states the same-ball property. Their weighted Proposition2.1 is related context. We apply the unweighted equation and derive all graph, box and weight adapters here. No source text or figures are reproduced.

To fit the ball geometry use the king graph on Z^D: neighbours have l-infinity distance1. Its radius-r balls have side L=2r+1 and volume L^D, hence volume regularity of order D. Verify its relative isoperimetry as follows. On an axis cube, averaging ordered-pair differences along canonical coordinate paths gives

    sum_B |u-mean_B u| <= (L/2)*sum_axis_edges |du|.       (2)

For an edge at cut t of its coordinate fibre, the number of ordered pairs whose canonical path crosses it is 2*t*(L-t)*L^(D-1). Dividing by L^D bounds its coefficient by L/2. The coordinate path stays inside the cube. Applying (2) to 1_A with |A|<=|B|/2 gives an axis edge boundary of size at least 2|A|/L. The source uses an INTERNAL VERTEX boundary, not an edge boundary: one boundary vertex has at most 2D axis edges, so its size is at least |A|/(D*L)>=|A|/(3D*r), for r>=1. The king-graph boundary contains this axis vertex boundary. This verifies precisely the source's relative isoperimetry. Omitting this edge-to-vertex factor would be an error; it is absorbed in kappa.

Apply source(2.5) on a king-graph ball. Each king edge is replaced by a coordinate path of at most D axis edges inside that cube. The q-power of its increment is at most D^(q-1) times the sum of the path increments' q-powers. Each axis edge occurs in only a D-dependent number of such paths (all their endpoints are within distance1 of that edge; a safe finite bound is 9^D). Thus the king gradient is bounded by a D-dependent multiple of the internal axis gradient. Normalized L2 is bounded by normalized Lq*, and the counting mean minimizes the L2 residual over constants. This proves (1) on odd cubes, with a uniform constant.

For a general indicated rectangle choose an odd integer L' equal to ell or ell+1 and extend it to the cube of side L' by reflecting each coordinate, with endpoint-repeating fold

    0,1,...,l_i-1,l_i-1,...,1,0,0,1,... .

The original rectangle is an initial subset of this cube. Since L'<=2*l_i+1, each original vertex and each original edge has at most four preimages in one coordinate; l_i=1 is extended constantly. Therefore the extension's axis q-gradient sum is at most 4^D times the original sum. Its original residual about mean_B is at most its residual on the extended cube about mean_cube. Writing the cube bound as kappa*ell^2*|cube|^(1-2/q)*(gradient sum)^(2/q), the inequality |cube|^(1-2/q)<=|B|^(1-2/q) follows because q<2. Absorb the reflection and graph constants into kappa. This completes the derivation of (1), including side length1 in a rectangle of maximum side2. Arbitrary values outside the cube may be assigned to the extension; the source inequality uses only internal edges.

## 2. The actual local weighted consequence

Put b(x)=m/a(x), mu(B)=sum_B b(x)^p, V=|B|. Weighted Holder, with q/(2-q)=p, gives

    (V^(-1) sum_edges |du|^q)^(2/q)
      <= (E_(a,B)(u)/V)*(V^(-1) sum_edges a(start)^(-p))^(1/p)
      <= (E_(a,B)(u)/V)*D^(1/p)*(V^(-1) sum_B a(x)^(-p))^(1/p).

Each vertex starts at most D internal positive-axis edges. Increasing kappa to absorb D^(1/p), equation(1) gives the DERIVED inequality

    sum_B |u-mean_B u|^2
      <= (kappa*ell^2/m)*(mu(B)/V)^(1/p)*E_(a,B)(u).     (3)

Apply this scalar statement to each actual real adjoint coordinate and field component, then add. The same coefficient profile and same box occur throughout; the constant does not acquire an h factor. No averaging of weighted energies or reassignment of a(start) is used. Singletons have zero residual regardless of (3).

## 3. Adaptive integer partition and its proved leaf count

Start from {0,...,n-1}^D. Split every coordinate interval of length>=2 into its floor/ceiling halves; length1 remains intact. A split produces at least2 and at most2^D children. At depth j, side lengths are the floor/ceiling of n/2^j until they reach1. Consequently every box has aspect ratio at most2, maximum side ell<=ceil(n/2^j)<=2n/2^j before the final depth, and V>=ell^D/2^D. Singletons are reached by J=ceil(log2 n); n=1 is treated directly.

Let

    alpha=2p-D>0,
    T=m^p/((c*kappa)^p*2^D).

Accept a nonsingleton B exactly when

    mu(B)*ell^alpha <= T;                               (4)

accept every singleton automatically, and split every other box. Equations(3),(4) and V>=ell^D/2^D imply c*residual_B^2<=E_(a,B). This is a terminating coefficient-based construction, not an assumed existence of good boxes.

Let B_j be the number of split (bad) boxes at depth j. Such boxes are disjoint, their mu masses add to at most M*n^D by (H), and each has mu(B)>T*ell^(-alpha). The preceding side bound yields

    B_j <= min(2^(jD), A*2^(-j*alpha)),
    A=M*(4*c*kappa)^p*(n^2/m)^p.                        (5)

Indeed the mass bound is M*n^D*T^(-1)*(2n/2^j)^alpha; D+alpha=2p produces exactly (5). The number of leaves is

    N=1+sum_split_nodes(number_of_children-1)
      <=1+(2^D-1)*sum_(j>=0) min(2^(jD),A*2^(-j*alpha)).

For A>=1, split this last series at j0=floor(log2(A)/(2p)). The increasing part up to j0 is at most [2^D/(2^D-1)]*A^(D/(2p)); the decreasing tail starting at j0+1 is at most A^(D/(2p))/(1-2^(-alpha)). For 0<A<1 the whole series is at most A/(1-2^(-alpha)). Hence, defining

    S=2^D/(2^D-1)+1/(1-2^(-alpha)),
    B_*=1+(2^D-1)*S,

we have in every case

    N <= B_* * max(1,A^(D/(2p))).                       (6)

No divisibility, even-side or power-of-two hypothesis on n was used. Terminal singleton masses need not satisfy(4): their residual is exactly zero, and the tree count charges their bad ancestors, not their mass criterion.

## 4. Original observation and explicit constant

Internal edges of different leaves are disjoint. All omitted inter-box and torus-wrap edges have positive energy, so summing the local inequality gives

    c*sum_(B,j) sum_B ||U_j-mean_B U_j||^2 <= E_a(U).

For C as in the statement, exact counting orthogonal decomposition is

    ||U||^2=sum_(B,j) sum_B ||U_j-mean_B U_j||^2+||C(U)||^2.

This proves the first part of(T) with actual Euclidean coordinates. Since m>=1, n/sqrt(m)<=sqrt(2)*n/sqrt(1+m). Substitution in(6) yields the safe explicit constant

    C_*=h*B_* * max(1,M^(D/(2p))*(8*c*kappa)^(D/2)).       (7)

This completes the analytic proof of(T). It is stronger than a statement requiring a Poincare certificate as input: (3), the partition and its dimension have all been derived from actual coefficients and the cited proved local Sobolev theorem. It does not establish (H) for any interacting model.

## 5. Strict weakening, limitations and novelty boundary

Relative pointwise ellipticity a>=eta*m implies(H) with M=eta^(-p). The converse fails uniformly even in the original exact-mean class: at one vertex set a=1, and elsewhere set a=(m-s)/(1-s), s=n^(-D). With m=n^(D/(2p)), n>=2, we have exact mean m, 1<=a<=2m, and normalized p-moment at most s*m^p+1<=2. Nevertheless min(a/m)=1/m tends to0. This is a genuine weakening of the sufficient pointwise condition, while (H) remains a distribution assumption. It is not a proof from the arithmetic mean alone. The compact-curl family of unit100 violates every fixed p>1 bound, so it does not contradict(T).

This note reuses classical weighted Sobolev/Holder and adaptive approximation ideas. The inspected primary local inequality is credited above. The literature search also identifies Birman and Solomyak's quantitative Sobolev approximation programme (publisher record https://doi.org/10.1090/trans2/114 ) and Sukochev--Zanin's torus Birman--Schwinger estimates (primary paper record https://doi.org/10.4213/sm9732e ). Those records establish relevant prior literature, NOT a checked equivalence of hypotheses or a theorem imported into the present finite lattice. A complete priority comparison has not been completed. No original spectral mechanism, independent discovery, or publication-grade novelty is claimed. The useful dossier contribution is the explicit actual coefficient/odd-box/normalized-observation adapter with a proved uniform count, grouped with the prior negative results.

The strict inequality p>D/2 is used in the geometric summation, through alpha>0. At p=D/2 the same local weighted argument is available (q*=2); the present counting proof only yields a logarithmic upper estimate of the form

    N <= 1+(2^D-1)*M*(c*kappa)^(D/2)*2^D
                         *(n^2/m)^(D/2)*ceil(log2 n).

This says nothing about whether that loss is necessary. No endpoint counterexample or sharp threshold is asserted.

## One next active question

For fixed D>=3,c>0,Nc>=2 and finite M, does the CRITICAL normalized moment mean((m/a)^(D/2))<=M, with actual scalar 1<=a<=2m and mean(a)=m, already imply(T) without a logarithmic loss? Mechanism to examine: finite-torus weighted inverse-operator counting or an adaptive construction beyond the above tree bound. Falsifier: an actual divergence-zero slow family meeting that exact critical moment while forcing unbounded rank relative to max(1,(n/sqrt(1+m))^D). Abandon/change route after three substantive units without a proved reduction or useful falsifier, recording the concrete obstruction. Current alpha=0 summation failure is a limitation of THIS proof, not a refutation. Formalizing the present theorem is preservation work, not a second new active research question.

## Model assessments and review context

FIRST exact-note assessment: 6/10 by the same preparing Codex agent; actual served backend identity and effort are not exposed. This is an identified self-assessment, not independent review, human peer review, editorial acceptance or a PDF assessment. Rubric0-10: analytic derivation7, originality3, dossier relevance8, verification maturity3; overall6 is a qualitative judgement, not a calibrated probability or arithmetic average. No score inherited from earlier notes/PDFs and no repeated review to improve a grade.

Audit performed on this exact note: graph volume and relative VERTEX boundary; canonical-path congestion; q and q* ranges; local rather than enlarged gradients; diagonal path multiplicity; reflecting odd extension and negative volume exponent; weighted Holder normalization and actual forward-edge start; finite termination and singleton exception; aspect ratio on odd splits; mass additivity, alpha and 4^p factor; geometric crossover for A<1/A>=1; leaf identity; actual output normalization/dimension; factor8 in(7); exact-mean strict-weakness family; endpoint logarithmic limitation. A draft edge-boundary/vertex-boundary omission was corrected before this first assessment. No computational run or kernel verification occurred in unit101; analytic checking is not labelled terminal reproducibility.

O1. The new graph/rectangle/partition/field adapters are not Lean-verified; the cited source theorem is an external analytic input.

O2. kappa is a finite D,p-dependent constant justified by that theorem and explicit bounded adapters, not a computed optimal value. Constants deteriorate as p approaches D/2.

O3. The theorem treats one scalar profile shared by all directions/components. No uncontrolled transfer to matrix, anisotropic, covariant or interacting coefficients is authorized by it.

O4. (H) is an extra distribution condition, not an original physical hypothesis proved or a consequence of arithmetic means. Pointwise ellipticity is weakened in this sufficient theorem only.

O5. Priority and significance remain limited by classical weighted Sobolev and adaptive approximation literature; independent novelty is unestablished. No standalone small paper is warranted.

O6. This source self-assessment supplies neither independent validation nor an exact-PDF review. Any future consolidated PDF needs its own exact-version checks and first assessment.

O7. Endpoint p=D/2 is open here; logarithmic counting loss does not show necessity. There is no physical interacting/continuum mass-gap conclusion. PR29 stays20/41, TermSource=0. No AIRR submission, deposit, acceptance or publication occurs in this unit.
