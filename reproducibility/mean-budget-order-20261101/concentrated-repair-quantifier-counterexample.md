# Mean budgets: attainable rank versus a fixed heterogeneous repair

Status: complete analytic finite-dimensional counterexample, not a new Lean endpoint, PDF, independent review or physical Yang-Mills result. Extends the single mean-budget matching-order question from units080/082. Base repository SHA41a9cd8a7a7742b5687560e65082484525bb2066; actual identity sources ComponentwiseFlatHodge.lean and ComponentwiseFlatGradient.lean. No change to frozen PDF97bdcba4... or its score.

## Quantifiers and statement

Fix D>=2, Nc>=2, n>=2, c>0, m>=0. Set r=Nc²-1, N=n^D, E=(R^r)^(sites x directions), dimE=DrN, with actual counting norm. Write a_(i,x,j)=max(1+w_(i,x,j),0). The counterexample has 1+w>=0, so the max introduces no change. All direction/component means are exactlym, stronger than the two-component upper budgets in unit080.

For a fixedw, let q(w) be the minimum real observation codomain dimension among the original admissible local nonlinear tuples. The oldq_*(n,m) minimizes over bothw and the observation. Those are different quantifiers. There is an explicit fixedw with

 q(w) >= max(Dr, r*((D-1)*N-D²+1)),

whereas the identity observation always gives q(w)<=DrN for thisw. Thus worst-case fixed-profile rank has volume order even when m=n² and W=max(1,(n/sqrt(1+m))^D)=1. There cannot be a uniform upper bound q(w)<=B(D,Nc,c)*W for every admissible profile. This does not refute the attainable/infimum theorem of unit080.

## Actual weights and exact means

Let0 be the actual all-zero torus site, e_i its positive unit neighbour. For everyi,j put

 a_(i,x,j)=m*N if x=0, and0 otherwise; w=a-1.

There areN sites for eachi,j, so (1/N)sum_x max(1+w,0)=m. No bound on individual positive amplitudes was imposed. Negative weights equal-1 away from0; this is within the stated signed-weight class. Whenm=0 all weights equal-1.

The repository proves, at its actual unordered-plaquette/counting normalization, Hodge(A)=sum_(i,x,j)||A_j(x+e_i)-A_j(x)||² for everyA, not only divergence-freeA (componentwiseFlatGradient_eq_hodge). componentwiseWeightedRepair_energy is the exact repair sum. Adding yields the actual total quadratic form

 Q_w(A)=sum_(i,x,j)(1+w_(i,x,j))*||A_j(x+e_i)-A_j(x)||²
       =m*N*sum_(i,j)||A_j(e_i)-A_j(0)||² >=0.

No abstract replacement form or supplied spectral certificate is used.

## Large actual zero-energy divergence-free space

Define the actual linear map B:E->(R^r)^(D x D) by B(A)_(i,j)=A_j(e_i)-A_j(0). Its codomain dimension isD²r, so rankB<=D²r. The actual flat divergence is div(A)(x)=sum_j(A_j(x)-A_j(x-e_j)). Summing over all sites cancels by torus translation. Hence div takes values in the actual mean-zero site space Z, dimZ=r*(N-1). To verify this dimension: summing site coordinates is ontoR^r (place the requested vector at one site), so rank-nullity gives ker(sum) dimensionrN-r.

Take T=(div,B):E->Z x (R^r)^(D x D), and V=kerT. Rank-nullity gives

 dimV >= DrN-[r*(N-1)+D²r] = r*((D-1)*N-D²+1).

This is a lower bound; no independence of constraints is assumed. Everyv inV is actually divergence-free and Q_w(v)=0, includingm=0. Negative right-hand sides are harmless; the separate actual constant-sector boundDr applies as well. n>=2 ensures the named neighbours are distinct, but the dimension lower argument does not require surjectivity ofB.

## Original nonlinear hypotheses force rank onV

LetC:E->F have derivativeL at0, C(0)=0. LetPhi(y)<=K||y||² for ||y||<delta, delta>0. Require c||A||²<=Q_w(A)+Phi(C(A)) for actual divergence-freeA in ||A||<radius, radius>0 andc>0. Forv inV withLv=0, the exact directional derivative gives C(tv)/t->0 as t->0. Both neighbourhood conditions hold for sufficiently smallt. Divide the inequality by t², use Q_w(tv)=0 and the penalty upper bound, and let nonzerot->0. Then c||v||²<=0, so v=0. This also works for arbitrary finite realK, using abs(K) if needed in the limiting estimate.

Thus L|V is injective and dimF>=dimV. The already verified actual constant-sector endpoint supplies dimF>=Dr. This is a necessity for every admissible observation of this fixed repair. Nonemptiness is explicit: C=identity intoE, Phi(y)=c||y||², K=c and any positive neighbourhoods give global coercivity sinceQ_w>=0. No hypothesis has been quietly moved into a structure.

## Falsifier and boundary checks

A claim of a universal fixed-profile upper boundB*W is falsified by settingm=n² and lettingn grow. W=1 and the displayed necessary rank diverges asn^D. WithD=2,Nc=2 the lower bound ismax(6,3*(n²-3)); n>=4 already gives39, while its identity upper bound is6n². These numbers are exact algebraic examples, not a numerical campaign. m=0 has Q=0 onallE and requires injection onkerdiv, consistent with the lower bound. n=2 and largeD may make the coarse lower bound negative; the harmonic floor remains valid. n=1 is excluded here and covered separately by the constant-sector theorem.

Mechanism is classical concentration of conductance leaving a large energy kernel plus rank-nullity and tangent coercivity. Originality/priority is not established; the contribution here is the explicit adapter and quantifier guard for the actual signed repair class. It does not address nonnegative repairw>=0, bounded contrast or uniformly elliptic conductances. It gives no interacting or continuum gap. No new question is opened: this closes a potential overstatement inside the same mean-budget order question.

## Model assessments and review context

First exact-note qualitative assessment6/10, by the same preparing Codex agent; served backend and reasoning effort unexposed. Not an independent model review, human peer review or editorial acceptance. Objections: O1 analytic proof not compiled in Lean; O2 rank-nullity/conductance localization are classical, novelty unestablished; O3 signedw with cancellation of the unit gradient term is essential, so no inference forw>=0; O4 fixed-profile maximum differs from the previously proved attainable infimum; O5 rank lower constant is not sharp and may be vacuous for small volumes; O6 no physical/continuum bridge; O7 this source grade must not be transferred to any modified source or PDF.
