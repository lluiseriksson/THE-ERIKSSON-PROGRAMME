# A global first reciprocal budget still permits many actual slow curls

Unit100,2026-11-02. Analytic refutation in the existing mean-budget dossier, not a new paper. Main base c722676fd5fa8b9a8c8e748b0eaa819e4c721ef1. No new Lean endpoint, physical interacting result or continuum mass gap is claimed.

## The question and the negative answer

Fix D>=3,Nc>=2 and ANY c>0. Does the combination of positive totals a>=1, exact global arithmetic mean m, upper bound a<=2m, and global first reciprocal mean <=2/m imply a profile-uniform bounded observation rank when m=n^2? No. We construct actual flat divergence-zero fields in disjoint weak boxes and derive a necessary rank growing as n^(D-2). This is not volume-order and the construction does not decide D=2 or stronger inverse-moment hypotheses.

All derivative directions and field components will use the same actual scalar coefficient a_(i,x,j)=a(x), so every directional arithmetic and reciprocal mean has the stated value/bound. These are GLOBAL means; no local-fibre budget is asserted. Repairs w=a-1 are nonnegative.

## Compact windows, with exact directed-difference constants

Choose an integer ell>=1 with ell>3D/c. On Z let

 t(r)=max(1-|r|/ell,0),
 T=sum_r t(r)^2=(2ell^2+1)/(3ell),
 V=sum_r (t(r)-t(r-1))^2=2/ell,
 W=sum_r (t(r+1)-2t(r)+t(r-1))^2=6/ell^2.

These sums have finite support. To check T, separate t(0)^2=1 and twice the sum of r^2/ell^2,1<=r<ell, then use sum r^2=(ell-1)ell(2ell-1)/6. The first difference has 2ell entries of magnitude1/ell. The second difference has entries1/ell,-2/ell,1/ell at -ell,0,ell. This also checks ell=1, giving T1,V2,W6. Forward and backward first-difference energies agree by translation.

Set P=2ell+2 and B=(2ell+1)^D. For n a multiple of P, place centres y=P*r+(ell,...,ell), r_i=0,...,n/P-1. The boxes

 W_y=y+[-ell,ell]^D

are disjoint, including across the periodic boundary, each of cardinality B. Each has an unused separating lattice layer. For any chosen centre define the zero-extended product on the actual torus

 psi_y(x)=product_i t(x_i-y_i),
 U^y_1(x)=(partial^-_2 psi_y)(x) H,
 U^y_2(x)=-(partial^-_1 psi_y)(x) H,
 U^y_j(x)=0 for j>=3,

where H is any fixed nonzero actual adjoint coefficient. The product is defined in the corresponding local integer box and set to zero elsewhere, not by an ambiguous representative on the whole torus. The available separating layer makes the displayed finite-difference calculations identical to their integer versions.

The actual flat backward divergence is

 partial^-_1 partial^-_2 psi_y H
 -partial^-_2 partial^-_1 psi_y H=0.

Translations in different torus coordinates commute, so this is an exact identity, not an approximate transverse projection. It agrees with gaugeConstraintQCLM_trivial_apply in PhysicalGaugeCochains.lean, which explicitly gives outgoing-minus-incoming backward differences. The NEW compact-window field construction itself is analytic, not Lean-compiled.

The field support is inside y+[-ell+1,ell]^D; the START SITES of all nonzero actual forward gradients lie in W_y. Counting norms and separability give

 ||U^y||^2=2 V T^(D-1)||H||^2>0,
 E_0(U^y)=2[W T^(D-1)+(D-1)V^2 T^(D-2)]||H||^2.

Here the derivative in the already differentiated coordinate contributes W; each of the D-1 other directions contributes V^2. The repository's actual componentwise finite flat Hodge identity identifies E_0 with the full squared forward-gradient energy. Consequently the EXACT Rayleigh quotient is

 lambda_ell=W/V+(D-1)V/T
           =3/ell+6(D-1)/(2ell^2+1)
           <=3D/ell<c.                                      (1)

For ell1 this is2D+1, consistent with the compact elementary curl. The smoothing window is essential to obtain (1) for arbitrary small fixed c. A sharp one-site/plaquette trap alone would only establish an obstruction for sufficiently large c; we do not silently use that weaker calculation for every c.

## Packing and exact arithmetic/reciprocal budgets

Now take n a sufficiently large multiple of P, for example n>=P^D, and set

 m=n^2,
 J=floor(n^(D-2)/B).

There are (n/P)^D available centres. Since P^D<=B*n^2 in this range, J does not exceed that number. Also n^(D-2)/B>=1, because D>=3 and n>=P^D>B. Thus

 J>=n^(D-2)/(2B)>0,                                      (2)

using floor(x)>=x/2 for x>=1. Choose any J centres, with W the union of their full boxes, and let

 s=|W|/n^D=B*J/n^D<=1/m,
 a(x)=1 on W,       a(x)=A=(m-s)/(1-s) off W.

Because m>=2 and s<=1/m<=1/2, A is well defined and

 1<=a(x)<=2m,       A>=m.

Indeed A-m=s(m-1)/(1-s)>=0 and A/m<=(1-s)^(-1)<=2. EXACT global arithmetic averaging gives

 (1/n^D)sum_x a(x)=s+(1-s)A=m.

The actual reciprocal mean is

 (1/n^D)sum_x 1/a(x)=s+(1-s)/A<=1/m+1/m=2/m.              (3)

These are direct identities/inequalities for the constructed coefficients, not a moment certificate supplied by an additional structure. They hold for every actual direction/component because all use the same a(x). Even the normalized upper contrast a/m<=2 is uniform. The relative lower coefficient1/m tends to zero.

For each U^y, every nonzero gradient starts in its weak box. Hence the TOTAL weighted energy Q_w(U^y), using baseline plus nonnegative repair, equals its unweighted E_0(U^y). Distinct boxes give disjoint field supports AND disjoint gradient start supports. Therefore for every real combination U=sum_y alpha_y U^y,

 ||U||^2=sum_y alpha_y^2 ||U^y||^2,
 Q_w(U)=sum_y alpha_y^2 E_0(U^y)=lambda_ell ||U||^2.

The actual divergence-zero span has real dimension J, with no abstract assumed band, injected surrogate or origin-map cost.

## Original local nonlinear data force unbounded observation rank

Let C:E->F obey C(0)=0 and be differentiable at0, with actual derivative Lambda and finite dimF=q. Let Phi(z)<=K||z||^2 near0 for finite real K, and suppose

 c||U||^2<=Q_w(U)+Phi(C(U))

on sufficiently small actual divergence-zero fields. If q<J, rank-nullity on the explicitly constructed span supplies a nonzero U with Lambda U=0. Along tU, C(tU)=o(|t|). Small t meets both actual neighbourhood conditions; divide the local inequality by t^2. Since K||C(tU)||^2/t^2 tends0, the limit yields

 c||U||^2<=Q_w(U)=lambda_ell||U||^2,

contradicting (1). No sign assumption on finite K is needed for that limit. Thus every such observation satisfies

 dimF>=J>=n^(D-2)/(2B)                                  (4)

along these multiples of P. Local radii, K, Phi and C may vary with n; c,D,Nc and ell are fixed. At m=n^2 the proposed matching-order expression max(1,(n/sqrt(1+m))^D) is exactly1, whereas (4) diverges for D>=3. Consequently GLOBAL first reciprocal control, even together with exact arithmetic means and a<=2m, cannot replace actual local-fibre distribution control in a universal fixed-profile upper guarantee.

This does not refute the infimum over profiles (constant a=m remains an upper witness), the previously derived explicit per-fibre inverse-budget sufficient condition, any asserted theorem under higher inverse moments, or any physical interacting/continuum statement.

## Why higher moments are a different question

From (2), s>=1/(2m) as well. For every fixed p>1 the constructed normalized inverse moment satisfies

 (1/n^D)sum_x (m/a(x))^p >=s*m^p>=m^(p-1)/2 ->infinity.

Thus these examples do NOT satisfy a uniform higher inverse-moment bound. No critical exponent for this actual rank problem is established here; the next question must include stronger explicit hypotheses if it is to survive this falsifier.

## Primary-source comparison and novelty boundary

Andres, Deuschel and Slowik, Harnack inequalities on weighted graphs and some applications to the random conductance model, arXiv1312.5473v6, https://arxiv.org/pdf/1312.5473 , inspected directly: section1.2 discusses dimension-dependent conductance/inverse-conductance moments; Theorem5.4 and the following trap construction (printedp38 onward) give a classical random-environment failure mechanism when their moment regime is weakened. Their theorem concerns ergodic laws and local limit statements, not this deterministic n-dependent counting-norm cochain observation-rank assertion. We do not import its conclusion or normalization. The finite compact-curl identities, packing and original nonlinear rank consequence are derived above. No priority or independent new-trap-mechanism claim. This result is grouped with the existing dossier, not a small standalone paper.

Source conventions checked directly in repository PhysicalGaugeCochains.lean:gaugeConstraintQCLM_trivial_apply and ComponentwiseFlatHodge.lean's actual curl/div-gradient identity at the retained formal source. This checks the analytic adapter's conventions; it does not pretend a new Lean proof exists for the windows/packing.
## Exact finite diagnostics and their limits

Own-Colab108, embedded fixture source1eb91fd91087b4ab521d449bf105debf5f7c1e99, exact fixtureSHA256b318522bb1e0a6847adbbebc8ac754b865427cd6267e0450eecd20f2d54d1e83 and driver763c8a31953ba147f1b50c572100e7ccfbf743d8080dd88a7d42bace713e72da. Six rational fixtures accepted in each of normal and optimizedPython,18actual mutations rejected in each mode. Checks used actual sparse fields and torus shifts, backwards divergence, active gradient supports, exact mean/reciprocal budgets, field/gradient disjointness, norm/energy identities and the nontrivial linear combination2U1-3U2. Mutations changed an actual field component, the actual strong conductance or an actual weak-support site; no acceptance relies on assert.

The first five fixtures use D/ell=(3,1),(3,2),(3,3),(4,1),(4,2), side n=2P and two traps, with m=1/s, to test the local identities/means. They are NOT fixtures of the asymptotic m=n^2 choice or all of its coarse sufficient thresholds. The sixth uses D3,ell1,n56,two traps,m3136=n^2; it satisfies the actual packing/budget even though the sufficient n>=P^D bound stated above is deliberately coarser. The general rank-growth proof is the analytic argument above, not extrapolation from six cases. General-theorem and new-Lean-run flags are explicitly false. Exact Rayleigh values are7,17/6,31/19,9,7/2,7, respectively.

Both modes exited0 in the own LinuxCPU/highRAM runtime,2026-11-02T13:17:58.743228Z–13:18:00.248641Z; runtime released and0active sessions/0rate observed. Full evidence archive6aa7f7c538f71836c11fa059fd45c02f9003b30b52acd756ab522f67e41e5fdc, report and inner manifest retained in the companion directory. This is one finite diagnostic batch, not two fresh-clone terminal reproductions or independent review. No local Windows mathematics was executed.

## Model assessments and review context

FIRST exact-note/source-and-diagnostic assessment6/10, same preparing Codex agent, actual served backend identity and reasoning setting unexposed. Assigned after reading the complete derivation and these finite outputs; no score inherited from period-two, internal-resistance, weighted-path or PDF artifacts. No repeat assessment to improve a grade. Qualitative rubric0-10: analytic consistency7, dossier relevance8, standalone originality3, formal verification maturity4; overall6 is a judgement, not a calibrated probability or numerical average.

O1. The complete compact-window, packing and nonlinear-rank theorem is proved here on paper, not Lean-compiled; finite diagnostics do not close this formal gap.
O2. Rare-trap and inverse-moment mechanisms are classical. The cited primary-source comparison does not establish priority for this finite deterministic actual-field adaptation; no new standalone paper is justified by this note alone.
O3. D>=3 and rank ordern^(D-2) are essential to this construction. No volume-order or D2 obstruction is proved here. Fixed small c is handled by a fixed wider window, not by claiming the sharp elementary curl has arbitrarily low energy.
O4. Six exact fixtures check convention/algebra/support failures only. Their different parameter choices are explicit; this is not exhaustive testing, a symbolic proof, a kernel run or independent reproduction.
O5. The example violates all uniform normalized inverse moments of orderp>1. It therefore leaves stronger moment conditions open, and it does not contradict the proved analytic per-fibre resistance sufficient condition.
O6. This6/10 is identified preparing-agent self-assessment only, backend/effortunexposed. No independent model review, human peer review, PDF score or editorial acceptance follows. Existing source/PDF grades are unchanged.
O7. Actual finite flat componentwise model only, no interacting/continuum gap; no new PDF, AIRR grant/send/deposit/acceptance/publication. PR29 remains20/41,TermSource=0.

## Route audit and exactly one next research question

After the implementation/consolidation units098/099, this unit tested a materially stronger coefficient relaxation instead of adding more small helper corollaries. The explicit compact-curl packing is a new useful analytic falsifier in this dossier, so it constitutes mathematical progress; no original physical hypothesis was removed. The first-reciprocal-mean question is closed negatively. Existing fibre/partition formalization is a consolidation backlog, not a second simultaneously active research question. Keep this result grouped with the existing paper dossier.

The ONE next active question is: for fixed D>=3,c>0,Nc>=2,p>D/2,M<infinity, do actual scalar profiles1<=a(x)<=2m with mean a=m and normalized inverse moment mean(m/a)^p<=M admit original local nonlinear observations of dimension at most C(D,c,Nc,p,M)*max(1,(n/sqrt(1+m))^D)? Mechanism to investigate: actual weighted Sobolev/capacity estimates and finite eigenvalue counting, with explicit real/divergence-free adapters. No sufficiency or sharp threshold is asserted. Falsifier: a packed actual divergence-zero slow family satisfying these higher-moment bounds while violating the rank order. Abandon after three substantive units without a proved coefficient-to-rank implication or useful new counterexample, recording learned scope and changing route or the concrete blocker. The classical random-walk moment theorem is context, not an assumed certificate or a solution of this question.
