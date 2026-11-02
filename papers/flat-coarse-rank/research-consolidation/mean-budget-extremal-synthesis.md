# Mean budgets: attainable rank, worst profiles and distribution control

Research consolidation draft, source only. This is not an issued manuscript version, rendered PDF, reviewed PDF, independent model assessment, AIRR submission or publication. Frozen21-page PDF97bdcba4413f330ba54cbaa14b66edc41fdaab8e7fbd3489c26a0788e4f385d0 is unchanged. Base24b007d6533621ef69997e770dda16d61baa0ee1. Consolidates one bounded question; no separate paper of corollaries.

## Common original class

Fix D>=2,Nc>=2,c>0 and the actual finite flat cochain/divergence/Hodge/gradient conventions. Let r=Nc²-1,h=Dr,n>=1,N=n^D,m>=1. Restrict here to actual nonnegative repair profilesw>=0 whose positive-total spatial means are<=m in every derivative direction for the two occupied field components0,1. These are the exact mean hypotheses used by the lower bound. The explicit profiles below satisfy means=m for all components and directions, so meet the stronger version as well.

For each suchw, q(w) is the minimum dimension ofF among observationsC:E->F differentiable at0,C(0)=0, with a locally upper-quadratic penalty and strict local coercivityc on the actual divergence-free domain. All original neighbourhood/derivative/penalty data remain explicit and may depend onn,m,w. No interacting or continuum identification is included. Identity observation withPhi=c norm² is admissible becausew>=0 givesQ>=0. Hence q(w) is a nonempty integer minimum, h<=q(w)<=hN.

Defineq_min as the minimum ofq(w) over this profile class andq_max as its maximum. The class is nonempty (w=m-1 is constant and nonnegative). Since attained integer values lie in the finite set{h,...,hN}, both extrema exist without a compactness assumption on the profile set. Put W=max(1,N/(1+m)^(D/2)).

## Unified extremal statement — analytic composition, not a Lean endpoint

Let A0=max(3,sqrt(8*pi²*D/c)), a=1/[2*(A0+1)^D],
B=2*h*max(2^(D/2),(1+sqrt(c/2))^D), and choose an integerk>=A0.
Set A=h/[2*(D+1)*k^D]. Then simultaneously

 a*W <=q_min<=B*W,                                    (I)
 A*N <=q_max<=h*N.                                    (II)

Thus the attainable repair/observation design and the most demanding fixed repair have different orders. More explicitly,

 (A/B)*min(N,(1+m)^(D/2))
 <= q_max/q_min
 <= (h/a)*min(N,(1+m)^(D/2)).                          (III)

This quantitative separation merely composes the preserved proofs; it is not counted as a substantial new mathematical advance or a new physical hypothesis elimination.

## Proof and coverage boundaries

For(I), the prior universal lower bound applies to every original admissible tuple with the two occupied positive-total means. The harmonic floor covers the small-volume regime; the actual integer quotient cutoff and full-tail mean-budget theorem cover the remaining regime, as derived in the unit080 analytic proof. Restricting to nonnegative profiles preserves this lower bound. Its compatible constant profilew=m-1 is nonnegative form>=1, and the actual real Fourier observation gives the upper boundB*W. All assumptions of the nonlinear class are fulfilled by that explicit global linear/quadratic construction. The uniform adaptive extremal theorem remains analytic even though its actual full-tail and harmonic ingredients have paired Lean evidence.

For(II), the identity gives the upper bound for every profile. Forn>=k, the explicit positive spike w_(i,x,j)=(m-1)N atx=0,0elsewhere has all positive-total means exactlym. The actual symmetric Fourier cube withR=floor(n/k),M=(2R+1)^D, actual divergence and actual origin-difference constraints give

 q(w)>=max(h,r*((D-1)*M+1-D²)), M>=N/k^D.

This is the analytic nonnegative-profile counterexample preserved at source19840421. To make a uniform all-volume bound explicit, letT=2*(D+1)*k^D. IfN<T, the harmonic floorh>=h*N/T=A*N suffices, whether or notn>=k. IfN>=T, thenn>=k and

 r*((D-1)*N/k^D+1-D²)>=r*(D-1)*N/(2*k^D)>=A*N.

The first inequality usesN>=2*(D+1)*k^D, and the second usesD-1>=D/(D+1). Therefore the explicit spike plus the harmonic floor suppliesA*N for alln>=1,m>=1. The profile class contains that spike, proving the lower bound forq_max. No independence of its finite constraints was assumed.

For(III), divide(I)-(II), usingq_min>=h>0. The exact elementary identityN/W=min(N,(1+m)^(D/2)) completes the proof. In particular form=n², the best attainable order is constant while the worst fixed-profile order is volume. Form fixed, both are volume order up to constants depending onD,Nc,c,m. There is no contradiction.

## Explicit distribution hypothesis that restores profile-uniform upper order

For a fixedalpha>0, assume in addition1+w>=alpha*m at every actual gradient index. Actual termwise energy comparison and the real Fourier threshold projection give

 q(w)<=h*max(2^(D/2),(1+sqrt(c/(2*alpha)))^D)*W.

Combining this explicit constructive upper bound with the same universal lower bound yields uniform matching order for every profile in this subclass. This is a sufficient extra hypothesis, not a consequence of means, an equivalence or an eliminated assumption. For compatibility with upper means andm>0, nonempty classes requirealpha<=1. The concentrated counterexample hasminimum total1 atm=n², hence relative lower ratio1/n², violating every fixedalpha eventually. Upper contrast control alone has not been proved sufficient in this dossier.

## Evidence and provenance matrix

| Claim or artifact | Evidence | Limit |
|---|---|---|
| Actual full integer-tail positive-total mean lower theorem | Proof067fed7556b9d5c2fb2e7672feafa20df4dda72e, paired ownColab094/094b, five exact endpoints | Does not itself formalize(I)-(III) |
| Actual constant-sector energy/injection/rank | Proof12201e2df4db0693b30b02600059f3264aa42048, paired098/098b, three exact endpoints, integrated PR139 | Harmonic baseline only |
| Adaptive attained order | Unit080 analytic source note | Not a new compiled endpoint |
| Nonnegative spike low-band obstruction | Source19840421f9fc510e33f973b4ce7956bed7d1bf05 analytic note | Full real-band/divergence dimension adapter not compiled |
| Relative lower-envelope upper construction | Sourcee2b007a9a9356add14e5f2ffd67d1818ef7cbe12 analytic note | Extra pointwise assumption; not a mean-only result |
| Concentrated energy adapter | Candidate7915ed1f, prepared099/099b at driver43374cf3 | UNEXECUTED, no formal PASS |
| Exact positive-total budget/site-map reuse | Candidate24b007d6, four target names | UNCOMPILED; stage2 only after stage1 |
| Frozen PDF97bd... |21pages individually visually inspected, first exact-PDF preparing-agent7/10 | Different bytes/scope; its grade does not apply to this draft |

The existing signedSiteGradientCLM is already the actual origin-difference map in PiLp packaging. Candidate map construction is not independent new work. The signed localized-energy module does not establish the positive-spike low-band count. Preserve failed095–097 pairs and the interrupted accidental096b restart; accepted098pair does not erase them. Latest verified public AIRR remainsv4 Working-paper—not admitted. Integration, working-paper deposit, AI assessment, human peer review and acceptance/publication are distinct.

## Model assessments and review context

This new consolidation source has a first qualitative preparing-agent assessment6/10, with actual served backend/effort unexposed. The same agent had the earlier proofs, logs and objections; it is neither independent nor blind. Complete objections: O1(I)-(III) and the positive-spike/divergence band count remain analytic; O2 the candidate stack is uncompiled and cannot support a formal coverage claim; O3 extremal quantifiers must stay distinct andm>=1 is necessary for this nonnegative class; O4 constants are deliberately loose and the synthesis adds no substantial new mathematics; O5 Fourier/rank-nullity/elliptic comparison mechanisms are classical and priority unestablished; O6 no physical interacting/continuum mass gap follows, PR29 remains20/41 andTermSource=0; O7 no inherited note/PDF grade, external model review, peer review, deposit or editorial acceptance is claimed. A future rendered PDF requires its own exact-byte assessment and visual review; this source assessment cannot replace either.

Primary-source context: Lin/Wan/Zhang, arXiv2403.06105v1Theorem1.2, https://arxiv.org/html/2403.06105v1 , for classical cyclic spectral background; all extremal quantifier compositions above are derived here. No claim that the source proves this exact nonlinear extremal statement or that an exhaustive novelty search has been completed.

## Delivery boundary and next step

This consolidates the existing dossier into one reviewable draft and a claim/evidence matrix. It does not alter the frozen approved-for-request artifact or issue another small paper. Formal route remains blocked by browser control, with one restoration request pending. On restoration execute frozen099/099b first, then stage2, preserve failures and verify runtime release. No further small source/corollary accumulation should be substituted for that execution debt. Publication still awaits its already-requested exact-artifact action; do not repeat either question.
