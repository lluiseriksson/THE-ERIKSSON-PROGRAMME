# Nonnegative repair still defeats a profile-uniform mean-budget upper bound

Status: complete analytic finite-flat counterexample, not a new Lean endpoint or PDF. Same single mean-budget matching-order question. Base98ad5d85e8dc5cfc0872fa7b70f629d1ba15c30b. This strengthens the concentrated-repair note preserved in PR140: its zero-energy construction used signedw; the present low-energy construction proves the obstruction even forw>=0 and total conductance>=1. Earlier source/score remains unchanged.

## Statement with explicit constants

Fix D>=2, Nc>=2, c>0; put r=Nc²-1, h=Dr. Choose any fixed integerk>=3 with 4*pi²*D/k²<=c/2. For every n>=k and everym>=1, letN=n^D, R=floor(n/k), M=(2R+1)^D. There is an explicit nonnegative repairw whose positive-total means are exactlym for every derivative direction and field component, and for which every original admissible nonlinear observation C:E->F satisfies

 dim_R F >= max(h, r*((D-1)*M+1-D²)).                    (1)

No neighbourhood, penalty or derivative constants need be uniform in n orm. The admissible class for this fixed profile is nonempty. For m=n², W=max(1,(n/sqrt(1+m))^D)=1, while (1) grows withn^D. Hence no upper bounddimF<=B(D,Nc,c)*W can hold uniformly for every fixed profile, even withnonnegative repair. The attainable infimum over profiles and observations is not refuted.

## Actual weights and energy, without cancellation of the baseline

For the actual origin0, all derivative directionsi and field componentsj, set

 w_(i,x,j)=(m-1)*N if x=0, and0 otherwise.

Thenw>=0 and1+w>=1. The exact site mean ofmax(1+w,0) is[N+(m-1)N]/N=m, including the two occupied components in the earlier mean-budget theorem. Using the actual identities componentwiseFlatGradient_eq_hodge and componentwiseWeightedRepair_energy, the total energy is

 Q_w(A)=sum_(i,x,j)||A_j(x+e_i)-A_j(x)||²
        +(m-1)*N*sum_(i,j)||A_j(e_i)-A_j(0)||².          (2)

These are the repository's actual torus shifts and counting norm. No replacement energy or supplied positive-form certificate appears. The baseline is present, andQ_w>=0 on allcochains.

## Construct and count the actual real low band

Use normalized cyclic characters exp(2*pi*i*<xi,x>/n), withxi in Omega={-R,...,R}^D. Since k>=3 andn>=k, R>=1 and2R<n; thus theM frequencies are distinct modulo n and Omega is closed under negation. The only self-conjugate frequency in this cube is0. Their actual real scalar span has dimensionM: the constant mode plus the real/imaginary parts of each nonzero conjugate pair. Orthogonality follows by summing the finite geometric series in each coordinate. Tensoring withD components andr real Lie coordinates gives a real subspaceU of dimensionDrM in the actual cochain space.

Each actual forward difference multiplies a character by exp(2*pi*i*xi_i/n)-1. Its squared modulus is4*sin²(pi*xi_i/n). Therefore onU, with the actual counting norm,

 Hodge(A)=sum_forward_edges||diff A||²
 <=beta*||A||², beta=4*pi²*D*R²/n²
 <=4*pi²*D/k²<=c/2.                                   (3)

This is a bound on every linear combination by diagonal orthogonality, not just on individual modes.

Actual backward divergence preserves this band. At a nonzero frequencyxi, its symbol is the nonzero row (1-exp(-2*pi*i*xi_j/n))_j. For each Lie coordinate its complex rank is1, hence a conjugate pair contributes real rank2r. The zero frequency contributes rank0. Thus div|U has real rankr*(M-1), and its actual kernelK=U intersectker(div) has

 dim_R K=DrM-r(M-1)=r*((D-1)*M+1).                     (4)

The complex computation is a counting device for this explicitly conjugation-stable real space; dimensions have not been doubled. For n>=3 the cyclic forward-difference convention matches the ordinary product-cycle spectrum, but (3) is derived directly, not imported under an incompatible short-period convention.

## Remove the concentrated spike by actual linear constraints

Define B(A)_(i,j)=A_j(e_i)-A_j(0), with codomain(R^r)^(D x D) of dimensionD²r. SetV=K intersectker(B). Rank-nullity on the restrictionB|K, without asserting its constraints independent, gives

 dim_R V>=r*((D-1)*M+1-D²).                            (5)

Everyv inV is actually divergence-free. Its concentrated repair term in(2) is exactlyzero. Combining(2)-(3) gives Q_w(v)<=c/2*||v||². This is an actual low-energy subspace even though all conductances are at least1; zero conductances and negativew are not needed.

## Original nonlinear data force injection onV

LetC(0)=0 andL=DC(0), letPhi(y)<=K0*||y||² on||y||<delta withdelta>0, and assume c||A||²<=Q_w(A)+Phi(C(A)) on actual divergence-freeA with||A||<radius, radius>0. These are the original hypotheses. Forv inV withLv=0, differentiability implies||C(tv)||/abs(t)->0. Divide the original inequality along nonzerotv by t² and let t->0; the penalty upper bound gives

 c||v||²<=Q_w(v)<=c/2||v||².

Sincec>0, v=0. ThereforeL|V is injective anddimF>=dimV. The already paired-verified harmonic baseline suppliesdimF>=h, proving(1). Fixed-profile admissibility is explicit: C=identity intoE, Phi=c||y||², K0=c and any positive neighbourhoods give global coercivity becauseQ_w>=0. No actual hypothesis was replaced by a structure field.

## Volume divergence and scope

For n>=k, R=floor(n/k)>=n/(2k), whence M=(2R+1)^D>=n^D/k^D. Consequently

 dimF>=r*((D-1)*n^D/k^D+1-D²),

with a positive leading constant depending only onD,Nc,c via fixedk. Settingm=n² leavesW=1 and makes this necessary rank diverge. This refutes the proposed uniform-in-profile upper order, while constantw=m-1 is still an available different profile attaining the earlier much smaller order. The two facts are compatible because their quantifiers differ.

Ifm=1 the spike vanishes and the argument reduces to the classical unweighted low-band rank obstruction; no discontinuity occurs. For smalln the lower bound(5) may be negative, so the harmonic floor matters. Whenm<1 the nonnegative repair class cannot have total meanm at all, so this statement correctly assumesm>=1. Unbounded contrast remains permitted by the mean-budget hypotheses; no inference is made for bounded-contrast profiles. It does not prove a physical, interacting-background or continuum mass gap.

## Primary sources, novelty and model assessment

The cyclic difference multiplier and spectrum are classical. Lin, Wan and Zhang, Connection Laplacian on discrete tori with converging property, arXiv2403.06105v1, Theorem1.2 gives the corresponding discrete torus spectral formula; inspected directly at https://arxiv.org/html/2403.06105v1 . Equations(2)-(5), real dimension bookkeeping and the original nonlinear adapter are derived above at the repository's actual conventions. No priority or originality claim is made for Fourier diagonalization, low-rank perturbation or rank-nullity.

First exact-note source assessment6/10 by the same preparing Codex agent; actual served backend and reasoning effort unexposed. This is not an independent model review, human peer review or editorial acceptance. O1 new adapters and real-frequency/divergence rank count are analytic, not Lean-compiled; O2 classical mechanisms, priority unestablished; O3 unbounded concentration/contrast is still allowed and essential to this chosen profile, so bounded-contrast questions remain separate; O4 numeric lower constants are loose and small-volume bound may be vacuous; O5 fixed-profile necessity must not be substituted for the attained infimum; O6 no interacting/continuum bridge; O7 no PDF change, inherited source score or automatic publication assessment. The old signed construction's score is not revised or reused as a review of these new bytes.
