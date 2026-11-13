# Source audit 300A — ACCEPT

Audited candidate SHA: `14f6c1afda58d925cdf1481ecb7791d0ade9395b`.
Judges SHA: `493d0aa62345fe537b7414f7cbc8d2a01d16b636`.
PR: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/247
Body capture method: `gh pr view 247 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid`; parse the JSON body, replace CRLF and CR by LF, remove all trailing LF characters, append exactly one LF, encode UTF-8 without BOM.
Normalized body: **992 bytes**, SHA-256 **`4e239b272a60914efaddca88198edf4ac59864eb78a0c268a08455951179adb9`**.
The captured headRefOid equals the audited candidate SHA. Both required mathematical files were read in full. No source or PR mutation was made.

## Verdict and its boundary

**ACCEPT** for the analytical assertions A–C at this exact source and for the registered G1–G7, with the nonblocking qualifications preserved below. The cutoff hypothesis implies the displayed explicit dimension-free normalized gap. The uniform-integrability consequence has correct uniform quantifiers. The escaped-moment conclusion is valid for the exact diluted balanced family of unit299, not a substitute construction.

This is a separate involved Codex/OpenAI source reading in the same environment. It is not independent-provider review, human peer review, formal verification, numerical validation, a PDF assessment, or a rating. No tests, Lean, builds, oracles, numerical/symbolic mathematical execution or Colab runs were performed. Reasoning was analytical; commands only read/capture sources and provenance, query git/PR state, write this evidence and hash bytes. No new paper, manuscript note or PDF was created. This acceptance does not establish historical originality or publication importance.

The judges are the immediate parent of the candidate commit and were not changed in the candidate. Their registration explicitly discloses preparatory reasoning. This is evidence of judges-before-candidate acceptance, not evidence of blind discovery or ignorance of the intended proof.

## G1 — support, Perron eigenvector, multiplicity, normalization: ACCEPT

All inner products use the uniform probability measure on a cube of size at least two. The Boolean noise operator has strictly positive transition entries for fixed 0<rho<1, is self-adjoint and has nonnegative Walsh eigenvalues rho to a nonnegative integer power. Consequently T is positive semidefinite and has a zero block outside S={r>0}. On S its entries are strictly positive. The support is nonempty because E r=1. Perron–Frobenius gives a simple positive top root and an eigenvector strictly positive on S.

When |S|=1, the full operator has only one positive eigenvalue and lambda2=0, with the remaining eigenvalues retained as zeros. There is no accidental removal of those zeros from the ordering. More generally, lambda2<1/2 is addressed before using sign parts. If lambda2>=1/2, a real second eigenvector is supported on S and orthogonal to the positive Perron vector. It necessarily takes both signs. This orthogonality is not a uniform-mean-zero assertion; neither equal sign masses nor u=v is assumed. A repeated second eigenvalue changes none of these facts: choose any real vector in that eigenspace, which is orthogonal to the distinct top eigenspace.

The unit vector sqrt(r) has Rayleigh quotient <r,P r>. Its constant Walsh contribution is (E r)^2=1 and every other contribution is nonnegative, so lambda1>=1. This is the required absolute normalization, not an assumed Markov normalization of T. The upper bound lambda1<=B_K follows from G2 and uses exactly the same probability convention. No counting-measure factor is missing.

## G2 — endpoint tail and total budget: ACCEPT

Set p=1+rho in (1,2). The conjugate exponents in Holder are 2/(2-p) and 2/p. For a unit L2 vector h and w>=0,

    E[w^(p/2)|h|^p]
      <= (E w^(p/(2-p)))^((2-p)/2) (E|h|^2)^(p/2).

Raising to 2/p gives ||sqrt(w)h||p^2 <= (E w^s)^(1/s), since p/(2-p)=s. The endpoint forward inequality for Q=P_sqrt(rho) therefore gives ||Q sqrt(w)h||2^2 <= ||w||s. The square on the left is essential: for w=r 1_{r>K}, its right side is at most (8^(-s))^(1/s)=1/8, so the norm itself is at most 1/sqrt(8). Replacing the norm by 1/8 would be an invalid strengthening; the candidate does not do so.

On {r<=K}, r^s<=K^(s-1)r, including r=0. Adding the controlled high tail gives E r^s<=K^(s-1)+8^(-s). Taking the 1/s power gives B_K, and maximizing the Rayleigh inequality gives lambda1<=B_K. K=1 causes no division by zero. The tail convention is strictly r>K throughout.

The signed multiplier estimate (7) is also correct. With q=2s/(s-1)=1+1/rho, Holder uses 1/s+2/q=1 and forward hypercontractivity maps L2 to Lq under Q. Applying the bilinear bound to unit inputs proves ||Q M_w Q||<=||w||s even for signed w. It estimates the transformed difference, not the square-root congruence difference directly. These two operators are not silently equated.

## G3 — normalized sign parts and quasi-norm interpolation: ACCEPT

Write h=u h_+ - v h_- with h_+,h_- nonnegative, disjointly supported and unit, u,v>0 and u^2+v^2=1. Pairing the eigenvalue equation with each sign vector gives exactly A_+=lambda2+(v/u)D and A_-=lambda2+(u/v)D. Positivity gives D>0, hence ||Q(sqrt(r)h_sign)||2>=sqrt(lambda2)>=1/sqrt(2) for each sign separately. The statement does not accidentally use the possibly small norm u or v of the unnormalized sign part.

Truncation is after multiplication by sqrt(r). The high part is precisely sqrt(r 1_{r>K})h_sign, so G2 applies with a unit input. The ordinary L2 triangle inequality yields a low-part norm at least 1/sqrt(2)-1/sqrt(8)=1/sqrt(8). Forward hypercontractivity then yields the low-part Lp lower bound. The low-part L2 norm is at most sqrt(K), since its squared norm is E[r h_sign^2 1_{r<=K}]<=K. No pointwise bound on h_sign is used.

For a=1-rho, solving 1/p=theta/a+(1-theta)/2 gives theta=(1-rho)^2/(1+rho)^2=1/s^2. Both Holder weights theta p/a and (1-theta)p/2 are strictly between zero and one and sum to one. Thus ordinary Holder applied to the powers of |g| proves interpolation even though a<1. There is no appeal to a quasi-norm triangle inequality. The interpolation statement holds for g=0 as well. The particular low parts are nonzero by their positive Lp lower bound, which justifies rearranging the inequality and taking positive inverse powers.

The resulting bound for each sign is

    ||f_low||a >= 8^(-1/(2 theta)) K^(-(1-theta)/(2 theta)).

The exponent of K is negative. Increasing K weakens, rather than improves, this lower estimate; the signs of the powers in the candidate are consistent.

## G4 — reverse estimate, compression and actual normalized gap: ACCEPT

The reverse hypercontractive parameter is the critical point that could have broken the proof. In Boolean notation the two-function condition is rho<=sqrt((1-a)(1-a)); here equality holds because a=1-rho. Thus the norm product in (5) has the correct exponent a, not p or sqrt(rho). For verification from the cited semigroup form, take the negative conjugate a'=a/(a-1); the time needed to map a to a' is one half of log((1-a')/(1-a))=-log(rho). Reverse Holder then gives the two-function inequality. The extension to functions with zeros follows by adding positive epsilon to each and taking a limit on the finite cube. No negative-power norm of a function with zeros is taken in the final inequality.

Positivity of the kernel and nonnegative truncands allows discarding both high parts in the cross term. Multiplying the two G3 bounds gives

    D >= 8^(-1/theta) K^(-(1-theta)/theta)
      = 8^(-s^2) K^(1-s^2).

The exponents are not halved or squared again. A possible concentrated sign part has already been controlled by the two lower truncated norms.

In the orthonormal sign basis the compression is [[A_+,D],[D,A_-]]. It has the exact eigenvector (u,-v) at lambda2; its other eigenvalue, computed from the trace, is lambda2+D(v/u+u/v)=lambda2+D/(uv). It is the larger one, since D>0. The variational principle bounds this larger compression eigenvalue above by the actual lambda1. This is the correct interlacing direction; no claim is made that the compression's other eigenvalue equals lambda1. Since uv<=1/2, lambda1-lambda2>=2D. Finally

    1-lambda2/lambda1 >= 2D/lambda1 >= 2D/B_K.

For the discarded case lambda2<1/2, nonnegativity and lambda1>=1 give gap>1/2. The boundary lambda2=1/2 belongs to the compression case. Combining the cases gives exactly the minimum in (2), and all its factors are positive for fixed rho,K. Rank one and repeated lambda2 are already covered. The result concerns the actual full eigenvalue ordering and the actual normalization, not unnormalized quadratic forms alone.

## G5 — UI, Orlicz-type hypothesis and quantifiers: ACCEPT

Fix rho first. For an entire sequence (or any family), condition (3) supplies a single finite K>=1 such that every density in the family obeys (1). Claim A then gives a single positive lower bound depending on rho and that K. Choosing a cutoff separately for each dimension would not suffice; the candidate explicitly takes the supremum before the cutoff limit. UI of r_L^s is equivalent to the displayed cutoff convention because a threshold M for r_L^s is K=M^(1/s).

For a single common nonnegative nondecreasing psi diverging at infinity and a single finite C controlling every E[r_L^s psi(r_L)], one can choose finite K with psi(K)>0 and psi(K)>=8^s C. On r_L>K, monotonicity gives the required tail estimate C/psi(K). The C=0 case is harmless. A uniform s+epsilon moment gives the stated K^(-epsilon) estimate. There is no assertion uniform in changing rho or changing psi.

The argument permits an arbitrarily large finite total moment bound across admissible families; it does not give one universal gap for all those families regardless of their tail modulus. The cutoff (or Orlicz-type data) remains an additional quantitative assumption. A bounded critical moment alone is still insufficient, and neither necessity nor equivalence of UI with a gap is asserted.

Terminology qualification: an arbitrary nondecreasing psi makes a valid weighted-moment criterion. It need not make t^s psi(t) a convex Young function, so this general statement should not be read as defining a Luxemburg Orlicz norm for every such psi. The concrete moment assertion and its proof do not require convexity and remain correct.

## G6 — exact unit299 construction, moment escape and spectrum: ACCEPT

The original `research/critical299/critical299A.txt` at `49705281f05ab18b71bd9ebc2da1985a0433340c` and its reproduction at `6f9b27f59e3b105a872c773ed4d38d027536655b:papers/marginal-transfer/evidence299/critical299A.txt` have identical git blob `650f87caf3fc972eb55350d6ef43b2fa12f1f094`, identical raw length 11309 and SHA-256 `00a0c712f9b929e3fb669356585c30f08bfd7a5218ea9d4a24121e5b26e00b03`. The candidate tree contains that same blob. The exact-critical theorem and proof in the referenced manuscript were also inspected. This is a real dependency check, not reliance on a prior ACCEPT label.

The undiluted q in 300 is the density called r in 299: delta_L=d L^(-1/3), w_delta=(1+delta x)/n(delta), R_L=product w_delta, a_L=kappa(delta_L)^(-L), Z_L=1+a_L m(delta_L)^L, q_L=(1+a_L R_L)/Z_L. The final r in 300 is the diluted tilde-r in 299, with exactly its piecewise epsilon_L and possible finite prefix. No construction has changed.

The inherited asymptotics were checked analytically from the explicit one-site formulas. The quadratic term of log n is (s-1)/2. In log kappa the rho/(1-rho) term cancels it. Hence L log kappa=O(L delta_L^4)->0 and a_L->1. Meanwhile L delta_L^2 diverges, so m^L->0 and Z_L->1. For fixed 0<t<s the coefficient of log E w^t is t(t-s)/2<0, giving E R_L^t->0, whereas E R_L^s=1 exactly. The elementary cross-power estimate in 299 then gives E q_L^s->2. Its theta=min(1,s/2) has both theta and s-theta strictly in (0,s), including s=2.

The spectral premise is justified by the source's actual Gram comparison. The two diagonal Gram blocks have largest eigenvalues exactly one; their off-diagonal block norm is sqrt(a_L) tau(delta_L)^L. The quadratic coefficient of log tau is -rho/[2(1-rho^2)], so this norm tends to zero. Weyl gives the upper first and lower second eigenvalue tending to one. For large L the second lower bound is positive and cannot be a spurious added Gram zero. The square X*X/XX* identity transfers all eigenvalues, including multiplicities, to the actual T_q.

The dilution epsilon_L vanishes because B_L->2^(1/s)>1; it enforces the exact norm budget via Minkowski. Its transformed perturbation norm is at most epsilon_L(1+B_L), which tends to zero by G2's signed estimate. Weyl and spectral equivalence therefore give both actual leading eigenvalues of T_r tending to one. No unproved preservation of a nonlinear moment by dilution is needed.

Markov's inequality using any fixed interior t makes R_L->0 in probability. Thus q_L->1 and the diluted r_L->1 in probability, on their varying cubes. The prior two-sign inequality, independently rechecked from the restricted Holder bound and disjoint sign sets, gives 2 lambda2(T_r)^s<=E r^s<=2. Squeezing proves E r^s->2 for the diluted family.

For fixed K>1, F_K(x)=x^s 1_{x<=K} is bounded and continuous at the limit point 1, although discontinuous at K. The elementary probability-neighborhood argument in 300 is valid across different probability spaces and yields E F_K(r_L)->1. Subtraction gives E[r_L^s 1_{r_L>K}]->1. It is crucial that K>1: continuity at 1 would fail at K=1. The claim excludes that endpoint. The finite prefix does not affect any limit; floors 0<b<1 are supplied by 1/Z_L->1. A floor b=1 remains excluded. This is an explicit failure of UI even with convergence in probability and a fixed positive floor.

## G7 — primary comparison, originality and relevance: ACCEPT with retained qualifications

[Mossel–Oleszkiewicz–Sen, arXiv:1108.1210v5](https://arxiv.org/pdf/1108.1210v5), introduction (1.1)–(1.2), the tensorization discussion and Remark 1.13 support the precise Boolean forward/reverse inputs. These mechanisms are classical; the paper credits the earlier reverse inequality to Borell. The parameter conversion in G4 was checked, rather than inferring a sharp Boolean exponent from the weaker general-product estimate.

[Wang, arXiv:1305.4460v6](https://arxiv.org/pdf/1305.4460v6), introduction and Theorem 1.1, uses an invariant Markov operator and an operator tail functional optimized over L2 inputs. Its uniformly integrable operator notion concerns output tails. This supports the candidate's comparison, not an identification with base-density moments. In finite dimension the per-operator tail limit is already zero; it alone gives no family-uniform quantitative lower bound.

[Miclo, author manuscript](https://perso.math.univ-toulouse.fr/miclo/files/2012/04/hyperboundedness.pdf), Section 5/Theorem 10 gives an Orlicz-norm extension; Section 6/Proposition 11 puts the quantitative threshold at **||M||_(L2->L4)^4=2**, not ||M||=2. Above that fourth-power budget, gaps can be arbitrarily small. The candidate's phrase “norm-budget transition at 2” should retain this explicit power when expanded; it is accepted as a compressed budget description, not as a competing raw-norm formula.

The measure distinction can be made exact without a new hypothesis: if phi is the unit positive Perron vector on S, the Doob operator is M f=phi^(-1) T(phi f)/lambda1 and its invariant probability is phi^2 times the uniform base measure. This is generally neither the uniform measure nor r times that measure. Multiplication by phi is an L2 isometry, but does not preserve higher-norm or density-tail cutoffs uniformly. An operator-tail theorem in that Perron measure cannot simply be applied to condition (1) by relabeling it “UI.” No quantitative bridge to those primary theorems was established here, and the candidate does not claim one.

Correctness is supported by the direct proof. Originality remains unresolved: this is an application of known hypercontractive, truncation and sign-compression tools, not a demonstrated new general principle about integrability and gaps. The audited specialized constant and escaped-moment calculation add a concrete conditional refinement to the existing transfer manuscript. They do not establish standalone-paper importance. The comparison was targeted, not exhaustive; absence of a located identical theorem is not priority evidence.

## Objections and limits retained intact

1. No total elimination of integrability: the uniform tail cutoff is load-bearing. Unit299 remains a valid negative case under mere critical moment control.
2. No uniform gap depending only on an arbitrarily large critical moment budget; the tail modulus matters. No optimal constant or necessity of UI has been established.
3. “Orlicz” must not imply an unproved Young-function property for arbitrary psi. The exact weighted-moment statement is valid as written.
4. Miclo's number 2 is a fourth-power norm budget. Omission of the power in a future numerical comparison would be misleading.
5. No new mechanism, external priority or standalone relevance is certified. The grouped-extension restriction is appropriate. Classical tools are acknowledged rather than renamed as discoveries.
6. No matching-marginal claim for this tilted family, fixed-range Gibbs claim, local dynamical gap, physical gap or continuum/Yang–Mills implication follows.
7. No numerical tests, source audit, prior PDF grade or provider label may be substituted for human peer review. This report supplies no new score and does not amend older negative/partial assessments.

None of these is an unresolved mathematical defect in A–C under their actual hypotheses. No gate returned FAIL or INEXECUTABLE and no registered gate was amended. The ACCEPT applies only to the identified source bytes and body, not to a later revision or a broader headline.

## Evidence and cleanup

The accompanying MANIFEST.json records raw SHA-256 and byte counts for retained subjects and report artifacts, their representations and the portions actually read. Git blobs were captured as bytes via `git cat-file blob`, without PowerShell text redirection or newline normalization. PDFs are the downloaded primary-source bytes, with targeted passages read through the web PDF reader. Whole-file capture is not a claim to have reviewed every theorem in those papers or the unrelated manuscript sections.

The only created directory is this retained evidence directory on D:. No disposable clone, worktree, runtime or service was created. The repository already had untracked `_drafts/` and `_tmp/`; they were neither inspected nor changed. No cleanup is pending for audit-created temporary clones.
