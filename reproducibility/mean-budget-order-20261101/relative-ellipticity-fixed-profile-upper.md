# Relative ellipticity supplies a universal fixed-profile upper witness

Status: complete analytic positive counterpart inside the same mean-budget matching-order question. Not a new Lean endpoint, PDF or independent review. Baseb6fb8a7091ef73374d1b8e06f17ccd6a091b9b7c. The explicit pointwise condition below is an additional sufficient hypothesis, not a hypothesis removed or hidden in a structure.

Fix D>=2, Nc>=2, c>0 andalpha>0. Let h=D(Nc²-1), n>=1, m>=0 and actual weightsw satisfy

 1+w_(i,x,j)>=alpha*m for every actual derivative/site/component index. (RE)

No upper bound onw is needed for this upper construction. If one also demands the earlier upper means<=m, nonempty classes withm>0 requirealpha<=1; we make no incompatible existence claim foralpha>1. Defineq(w) as the minimum dimension of an observation satisfying the original local nonlinear coercivity for this fixedprofile. There is an explicit global linear observation with quadratic penalty giving

 q(w)<=B*max(1,(n/sqrt(1+m))^D),
 B=h*max(2^(D/2),(1+sqrt(c/(2*alpha)))^D).                (1)

In particular if all actual total conductances are in[alpha*m,beta*m] for fixedalpha>0, the mean-budget upper order holds uniformly over every such profile. Upper contrast control alone is not proved sufficient here. The earlier concentrated nonnegative profile has minimum total1 andm=n², so its best relative lower ratio is1/n²; it violates every fixedalpha>0 eventually. This explains precisely which extra distribution control the positive theorem uses, without contradicting the counterexample.

## Actual energy comparison

The repository's actual global flat identity gives

 Q_w(A)=sum_(i,x,j)(1+w_(i,x,j))*||A_j(x+e_i)-A_j(x)||²
       >=alpha*m*sum_actual_forward_edges||diff A||².   (2)

This holds on every cochain, so in particular on the original divergence-free domain. It follows by termwise multiplication of(RE) by nonnegative squared differences, not an assumed certificate. Q_w>=0 even whenm=0.

For0<=m<=1 takeC=identity into the actual cochainE andPhi(y)=c||y||². This proves global coercivity andq<=h*n^D. Withx=n/sqrt(1+m), n^D=(1+m)^(D/2)*x^D<=2^(D/2)*x^D, proving(1) in this range, includingm=0 andn=1.

## Actual real Fourier observation for m>=1

Use all actual cyclic residues, represented by centred integerskappa_i withabs(kappa_i)<=n/2 (one representative for each residue, retaining a single Nyquist residue for evenn). The actual forward-difference multiplier has squared modulus4*sin²(pi*kappa_i/n). Its sumlambda(kappa) is unchanged by residue conjugation. Counting-norm orthogonality diagonalizes the gradient form.

LetP be the actual real orthogonal projection onto exactly those scalar modes withlambda<c/(alpha*m), for all field and Lie coordinates, and letF=rangeP with its actual Hilbert norm. Conjugation symmetry makes this a real subspace; its real scalar dimension is the numberL of selected residues. Non-self-conjugate residues pair into two real dimensions, each self-conjugate residue contributes one. Thus dimF=h*L, with no doubled complex count. TakeC=P:E->F andPhi(y)=c||y||². Low/high orthogonality gives

 alpha*m*gradient(A)>=c*||(I-P)A||²,
 Phi(C(A))=c*||PA||²,

and(2) proves c||A||²<=Q_w(A)+Phi(C(A)) for everyA. The cutoff is strict on the selected band, so equalitylambda=c/(alpha*m) belongs to the high band and satisfies the required non-strict inequality. No penalty-neighbourhood or derivative assumption is merely postulated: linearC is differentiable withC(0)=0, andPhi=c||y||² has global upper boundK=c. Any positive neighbourhoods work.

## Counting and boundary normalization

Forabs(kappa_i)<=n/2, concavity ofsin on[0,pi/2] gives sin(pi*abs(kappa_i)/n)>=2*abs(kappa_i)/n. Hence lambda>=16*sum_i kappa_i²/n². A selected residue therefore has

 abs(kappa_i)<(n/4)*sqrt(c/(alpha*m)).

An open interval(-t,t) has at most1+2t integer points. Intersecting with the centred representative set cannot increase this count, even at the Nyquist boundary. Thus

 L<=min(n^D,(1+(n/2)*sqrt(c/(alpha*m)))^D).

For m>=1 andx=n/sqrt(1+m),

 (n/2)*sqrt(c/(alpha*m))
 =sqrt(c*(1+m)/(4*alpha*m))*x<=sqrt(c/(2*alpha))*x.

Finally1+a*x<=(1+a)*max(1,x), giving(1). This uses the actual directed cyclic-difference convention; n=2 is not silently replaced by a simplegraph with only one edge between its vertices. At n=1 only the constant residue remains,lambda=0 andP=identity, consistent withq=h and(1). The argument is independent of whether the actual fixed profile is spatially constant.

## Relation to earlier results and novelty

The attained-infimum upper witness of unit080 chose constantw=m-1; the present witness works for every fixed profile satisfying the explicit lower bound(RE). Unit085 shows(RE) cannot be inferred from upper means andw>=0: concentrated profiles violate it and force volume-order observations at m=n². This is a sufficient-condition theorem, not an equivalence or a proof that all failures of(RE) force large rank. No interacting-background or continuum mass gap follows.

The Fourier multiplier is classical; primary context is Lin/Wan/Zhang, arXiv2403.06105v1Theorem1.2, https://arxiv.org/html/2403.06105v1 , inspected previously. The actual short-period convention, real count and threshold projection are derived here. No priority claim for elliptic comparison or Fourier diagonalization.

Model assessments and review context: first exact-note source6/10 by the same preparing Codex agent, actual served backend/effort unexposed. No independent model review, peer review, acceptance or inherited PDF grade. O1 analytic projection/counting adapters not Lean-compiled; O2(RE) is additional and not derived from mean budgets; O3 this sufficient condition is not necessary and constants are not sharp; O4 upper contrast alone has not been analysed here; O5 mechanisms classical, novelty unestablished; O6 no physical/continuum bridge; O7 no frozen-PDF edit/new paper and no transfer of this source grade to any future manuscript.
