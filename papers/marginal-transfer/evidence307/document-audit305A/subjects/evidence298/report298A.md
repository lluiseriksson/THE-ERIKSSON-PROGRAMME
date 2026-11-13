Hash context: frozen Git commit `2d1d27c4ba5f677e7f51092c6479735ba9ba59fa`; source Git-blob/LF SHA-256 `e68c9d1c168323123ce639268877b2cc5b544fc418dab8d54ff59667f9502fe7`; actual-checkout raw SHA-256 `e68c9d1c168323123ce639268877b2cc5b544fc418dab8d54ff59667f9502fe7`.

# Critical298A analytical source audit

**Verdict: ACCEPT for the stated analytical source and unchanged gates G1-G8.** No blocking mathematical defect was found. The two theorems establish a sufficient small-budget region and collapse for every fixed B>2 at the critical exponent. They do not identify an optimal budget, settle all intermediate budgets, establish external originality, or certify any PDF, publication or physical interpretation.

This verdict refers to the exact commit and source bytes above, not to the branch's future contents. The auditor was a separate Codex/OpenAI subagent. Technical isolation, served model/backend and reasoning settings are unverified. This is involved model-assisted analytical review, not independent human peer review or formal verification. No numerical score is created.

## Referent and evidence

- Worktree: `C:\Trabajo\the-eriksson-programme\prefix-rank290-20261113`.
- Branch observed: `codex/tep-critical298-20261113`.
- Frozen HEAD observed: `2d1d27c4ba5f677e7f51092c6479735ba9ba59fa`.
- Gate registration: `c4f88b14b0ef615153365a7d2feed5d0227c5881`.
- Gate Git object at both registration and target: `3a3b5f27f887b8590d76b2ed9020c09346b5d66a`.
- Gate SHA-256, Git-blob/LF and separately actual checkout raw: `2bd465dc190781cb940d998295c59c80f476465bfb6bc3551a1126a4edbc8dc1` (2640 bytes each).
- Candidate source: 9194 bytes in each separately captured representation. Git eol metadata says LF for both the Git source and actual checkout. Thus equality of these two hashes was observed, not assumed.
- Evidence directory: `D:\Datos\the-eriksson-programme\autonomia\evidencia-298\source-audit298A`.

`input-manifest.json` records all frozen local source representations. `output-manifest.json` records the completed evidence files, excluding itself to avoid self-reference. `assignment-received.txt` preserves the exact visible assignment text. `context-and-scope.txt` states the actual reading scope and limitations. `primary-source-reading-notes.md` distinguishes inspected primary-source statements from unverified novelty. Frozen copies are retained under `subjects/git-lf` and `subjects/checkout`.

No PR existed in the assignment; no PR body was received or audited. Consequently PR-body capture, body normalization and body hash are not applicable. No gate was altered. The gate's own statement that registration followed candidate development is retained: this is not blind pre-discovery registration.

## G1 — normalization, positivity, fixed moment budget and density floor: ACCEPT

All integrals and norms use uniform probability, not counting measure. The Walsh functions 1 and x are orthonormal in the one-bit space. For each nonzero tilt with |delta|<1, n(delta)>1 by strict convexity, w_delta is strictly positive, E w_delta=1/n=m in (0,1), and E w_delta^s=1 exactly. Tensor product probability therefore gives ||R_L||_s=1 and E R_L=m_L^L. No factor 2^L is missing.

With a_L>0 and Z_L=1+a_L m_L^L, r_L=(1+a_L R_L)/Z_L has exact mean one and is strictly positive. Once a_L<=B-1 is proved under G5, triangle inequality gives ||r_L||_s <=(1+a_L)/Z_L<=B, while Z_L<=1+a_L<=B gives r_L>=1/Z_L>=1/B. These are separate inequalities; positivity of the numerator is not being mistaken for a dimension-independent floor. They hold for every L>=1, not only asymptotically.

Theorem A permits zeros and only assumes nonnegativity and mean one. Its setup correctly includes the full eigenvalue list with zeros. Mean one prevents the operator from being zero. The finite-dimensional Hilbert-space statements therefore also cover a density supported at a single point.

## G2 — endpoint exponents and the actual transfer spectrum: ACCEPT

Q=P_sqrt(rho) has Walsh multipliers rho^(|S|/2), is self-adjoint and positive definite, fixes 1, and squares to P_rho. The source uses q=2s/(s-1), so 1/s+2/q=1 and q-1=(s+1)/(s-1)=1/rho. The ordinary hypercontractive boundary for input exponent 2 is theta<=1/sqrt(q-1); theta=sqrt(rho) satisfies equality. The endpoint is included, with a dimension-independent norm-one constant. This matches equation (1.1) and the tensorization statement in the directly inspected [Mossel-Oleszkiewicz-Sen primary manuscript](https://arxiv.org/pdf/1108.1210).

For real f,g, Holder yields |<Qf,(r-1)Qg>|<=||r-1||_s ||Qf||_q ||Qg||_q, hence ||Q M_(r-1)Q||<=||r-1||_s. Real vectors suffice for these real symmetric matrices; the same bound extends to complex vectors by positivity if desired. S_r-P_rho is exactly that operator. Since the second eigenvalue of P_rho is rho for every L>=1 (multiplicity L is harmless), the variational bound is lambda_2(S_r)<=rho+||r-1||_s.

The equality of the spectra of T_r=AA* and S_r=A*A, A=M_sqrt(r)Q, is valid including multiplicities and zeros because A is square. It does not require invertibility in Theorem A. Also <1,S_r1>=E r=1, with ||1||_2=1, gives lambda_1>=1. Since lambda_2>=0, lambda_2/lambda_1<=lambda_2. Thus gap>=1-rho-||r-1||_s. Combining this with the trivial nonnegative gap proves the stated maximum. No comparison with a different generator or stationary-law density enters.

## G3 — complete scalar estimate for both exponent ranges: ACCEPT

The subtraction in phi_s(t)=t^s-1-s(t-1) is essential and correct: its mean is E r^s-1 because E r=1. For s>=2 and t=1+u, integrating (1+v)^(s-1)-1>=v^(s-1) gives phi_s(t)>=u^s. The displayed elementary inequality follows from the nonnegative derivative of (1+v)^a-1-v^a for a>=1.

For t=1-u with 0<=u<=1, the derivative of phi_s(1-u)-u^s is s[1-(1-u)^(s-1)-u^(s-1)]>=0: both powers are at most their bases. The difference is zero at u=0. This proves phi_s(t)>=|t-1|^s on both sides of 1, including t=0 and s=2. Taking expectations and the s-th root yields the first formula without an omitted constant.

For 1<s<2, Taylor's integral remainder is phi_s(t)=s(s-1)(t-1)^2 integral_0^1 (1-v)[1+v(t-1)]^(s-2) dv. At t=0 the integrand reduces to (1-v)^(s-1), which is integrable; extension to this endpoint is legitimate. The negative exponent reverses the comparison of bases, so bounding the base above by t+1 produces the stated lower bound with the factor 1/2. This sign was explicitly checked.

For W=(r-1)^2/(r+1)^(2-s), one has |r-1|^s=W^(s/2)(r+1)^(s(2-s)/2). Holder with exponents 2/s and 2/(2-s) therefore gives exactly the source's estimate. After the s-th root, the second factor is ||r+1||_s^((2-s)/2), not a different power. Minkowski bounds this by (B+1)^((2-s)/2). Combining with E W<=2(B^s-1)/(s(s-1)) proves the second formula. There is no singular division by r.

Both bounds tend to zero as B decreases to 1 for each fixed s>1. Since 1-rho>0 is fixed, some B_0>1 exists. At B=1 the estimate is exact: r=1 and gap=1-rho. No uniform B_0 as rho approaches 1 is claimed or needed.

## G4 — one-bit eigenvalue, cross norm and analytic remainders: ACCEPT

Multiplication by w_delta has Walsh matrix n^-1[[1,delta],[delta,1]], so sandwiching by diag(1,sqrt(rho)) gives exactly H. Its determinant is rho(1-delta^2)/n^2>0 and its trace is positive, establishing positive definiteness. The quadratic formula gives the stated kappa with the positive square-root branch.

For K=D^(1/2)H^(1/2), KK*=D^(1/2)H D^(1/2)=n^-1[[1,rho delta],[rho delta,rho^2]]. Consequently tau^2=lambda_max(KK*) has precisely the source's formula. This directly checks the noncommuting square-root order and avoids inferring a norm from the eigenvalues of the unsymmetrized product. The formula is valid for either sign of delta and at delta=0.

Analytically, averaging (1+delta)^s and (1-delta)^s leaves the coefficient s(s-1)/2 at delta^2. Taking log and dividing by s yields (s-1)/2. Expanding each positive radicand at zero gives the numerator coefficients rho/(1-rho) for kappa and rho^2/(1-rho^2) for tau^2. Thus the quadratic coefficient of log kappa vanishes at the stated critical s. The coefficient of log tau is

    (1/2)[rho^2/(1-rho^2)-rho/(1-rho)]
      = -rho/[2(1-rho^2)] < 0.

This checks the decisive sign and both factors of two. All bases remain positive on a sufficiently small closed interval strictly inside (-1,1), and the eigenvalue radicands are positive at zero for fixed 0<rho<1. The log functions are even real analytic there. A bounded fourth derivative gives |log kappa|<=C delta^4 after increasing C to at least 1. The same remainder control in log tau allows c=rho/[4(1-rho^2)] after reducing delta_*. The constants need not be explicit numeric values: the theorem asserts existence, and the compact-neighborhood argument proves it. No uniformity over rho approaching the endpoints is claimed.

An extra consistency check is available: the endpoint Holder estimate applied to one-bit w_delta with ||w_delta||_s=1 gives ||H||<=1, hence kappa<=1. The source does not rely on this sign, so an unknown quartic sign cannot undermine the proof. There is no forbidden symbolic or numerical calculation behind the coefficient checks.

## G5 — balancing, limit and all-L budget: ACCEPT

For B>2, log(B-1)>0. A fixed positive d<=delta_* with C d^4<=log(B-1) therefore exists. For every integer L>=1, delta_L=d L^(-1/3) remains in the analytic interval and is nonzero. The scale satisfies

    L delta_L^4 = d^4 L^(-1/3) -> 0,
    L delta_L^2 = d^2 L^(1/3) -> infinity.

The first expression bounds |L log kappa(delta_L)|. Thus kappa(delta_L)^L tends to 1, a_L=kappa(delta_L)^(-L) tends to 1, and |log a_L|<=C d^4 L^(-1/3)<=log(B-1), proving a_L<=B-1 for every L. rho,s,B,d,C,c are fixed; only tilt and the explicitly balanced amplitude depend on L. The moment budget itself never changes with L.

The balance is exact, not a first-order approximation: the top eigenvalue of a_L H(delta_L)^(tensor L) is a_L kappa_L^L=1. This eliminates the residual mismatch between the two channels. B=2 is excluded because the simple choice condition becomes C d^4<=0; the source correctly does not infer an endpoint-budget theorem from this construction.

## G6 — Gram equivalence, multiplicity, small dimensions and gap ratio: ACCEPT

Tensorization gives Z_L S_rL=P_rho+a_L H^(tensor L). All factors are positive definite. For C_L=[P_rho^(1/2),sqrt(a_L)X_L^(1/2)], the two Gram matrices have the stated dimensions N by N and 2N by 2N. C_L has rank N because its first block is invertible. Thus C_L C_L* has exactly N positive eigenvalues, and C_L*C_L has exactly these with multiplicity plus N zeros. Since N=2^L>=2, the first two labels transfer without any ambiguity even at L=1.

The diagonal block comparison has two top eigenvalues exactly 1, one from each channel, and no eigenvalue above 1. Positive square roots tensorize, and the operator norm of a tensor product is the product of its norms. Therefore the cross-block norm is exactly eta_L=sqrt(a_L) tau(delta_L)^L. The self-adjoint off-diagonal perturbation [[0,K],[K*,0]] has norm ||K||, by squaring it. The variational inequalities are therefore lambda_1<=1+eta_L and lambda_2>=1-eta_L.

The lower estimate for lambda_2 may be negative at small L; the proof neither assumes otherwise nor discards those dimensions. F_L>=P_rho gives lambda_1(F_L)>=1 independently. Subtracting the two variational estimates yields lambda_1-lambda_2<=2eta_L, and division by lambda_1>=1 gives gap<=2eta_L. This avoids incorrectly dividing by 1-eta_L or assuming the bound is less than 1. Combining G4 and G5 gives eta_L<=sqrt(B-1) exp(-c d^2 L^(1/3)), which tends to zero.

Dividing by the positive scalar Z_L and passing between square AA* and A*A preserve eigenvalue ratios. In the configuration basis, each one-bit noise transition has entries (1+rho)/2 or (1-rho)/2, all positive; their product and multiplication by sqrt(r_L)>0 remain strictly positive. Perron simplicity proves strict gap positivity at each finite L. No orthogonality of channel eigenvectors, exact degeneracy of the actual transfer matrix, or asymptotic replacement of the leading eigenvalue was assumed.

## G7 — precedent, classical inputs, novelty and scope: ACCEPT with explicit limits

The frozen manuscript297A.tex states a uniform gap for each finite budget when s>s_c and collapse for every B>1 when 1<s<s_c, while leaving s=s_c unresolved there. Its normalization matches the new source. Its strict-regime positive proof loses its interpolation room exactly at criticality; its fixed-tilt negative proof needs a positive quadratic coefficient. The new small-budget perturbation estimate and dimension-dependent balanced construction address that gap without claiming the strict-regime proofs automatically extend.

I read the complete two-tilt297A proof and the relevant manuscript sections. Its final fixed additive uniform-block error is proportional to kappa^(-L); at the present scaling kappa^L tends to 1, so that error does not vanish. Including the uniform channel in the new Gram matrix is therefore a material repair of the argument. It is not permissible to reuse the old error estimate as if it proved endpoint collapse.

The ordinary endpoint input was checked in a primary research manuscript. The threshold itself and norm-one inequality are classical. [Gross's Theorem 2.2](https://arxiv.org/html/2412.20282v2) supplies genuine dimension-independent perturbation results in an additive Schroedinger setting. This audit established no operator/exponent correspondence to the present multiplicative transfer congruence, and it does not certify that no such deduction exists. The positive floor here already supplies inverse-density moment bounds; lack of inverse control cannot distinguish this counterexample from all such literature. The source appropriately asserts no priority or optimality.

The public deposited v2 file and publication status were not independently verified; this comparison concerns the exact frozen predecessor manuscript named in the assignment. No broad novelty clearance is inferred from this limited source check. Nonlocal logarithmic weights, no matching low-order marginal assertion, uniform-reference rather than Perron-law moments, and no heat-bath or Yang-Mills gap claim are all explicitly preserved. The still-open intermediate critical budgets must remain visible in manuscript integration.

## G8 — failed routes, analytical status and audit boundary: ACCEPT

The source explicitly retains the three-channel B>3 preliminary route, the failure of the earlier fixed additive error at critical scaling, and the unbalanced a_L=1 mismatch. The last route's generic residual is of polynomial order from 1-kappa_L^L, while exact balancing removes it. These are honestly labelled author development, not failed external gates or certified results. The source states that no computation or formal verification was performed. This audit likewise performed only analytical reasoning and metadata/evidence work, not local mathematical computation, tests or builds.

There was no inbound message after the assignment and no contact with other chats. No source or gate was modified. Separate role execution is observed at the subagent level; strong technical or provider isolation is not verified and is not claimed. Gate identity is established by equal Git blob IDs at the registration and target commits, supplemented by separately captured raw SHA-256 values.

## Disposition

The proof meets the registered target without a weakened gate or mathematical repair. No blocking objections remain within this source audit. Preserve this exact audited commit as the referent; later manuscript additions or changes require their own appropriate review. The acceptance is mathematical-source acceptance only. It grants no PDF score, novelty priority, optimal-budget conclusion, publication acceptance, or human-peer-review status.

No disposable clone was created. No cleanup is pending.
