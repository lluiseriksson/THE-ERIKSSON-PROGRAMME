# Separate analytical source audit 301A — ACCEPT

Candidate SHA: `6bc50cc52599b0df915895458002a3245e78e343`.
Registered judges SHA: `758e1c5d8d40f3ce4717fc4885c29a5f9dec3559`.
PR: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/248
Body capture: `gh pr view 248 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid`.
Normalization: parse JSON body; replace CRLF and CR with LF; remove all terminal LF characters; append one LF; encode UTF-8 without BOM.
Normalized body: **874 bytes**; SHA-256 **`6640eb52c35caf10786c51ec49c146ee8f131288fc5011be56d6c2439749a090`**.
The captured PR head is the candidate SHA. Judges are its immediate parent; the candidate does not modify them.

## Verdict and review context

**ACCEPT** against all six registered gates. For every fixed 0<rho<1, every finite M>1, every B>M^(1/s), and every 0<b<1, the construction has the claimed normalized mean, floor, norm budget, limiting moment M, escaped moment M-1, actual limiting gap 1-rho and all-dimension lower gap (1-rho)/2. The finite prefix replacement is a legitimate part of the existential construction. No condition on M relative to 2 is needed.

The conclusion is the nonnecessity of critical-power uniform integrability for existence of a dimension-uniform gap. It is not a sufficient criterion based only on the total critical budget, nor does it remove a hypothesis from theorem300. There is no contradiction with the collapsing families of299.

This is a separate involved analytical audit in the same Codex/OpenAI environment. The auditor retains its prior source-audit300 context, including the full readings of299 and300. It is not a fresh blind context, independent-provider review, human review, formal verification or a PDF assessment. No numerical grade is issued or inherited. The new candidate and judges were both read in full; the proof below was rederived analytically. There was no local mathematical execution, test, build, Lean, oracle, numerical experiment, runtime or symbolic script. Commands only read/captured sources and metadata, wrote evidence and hashed bytes. No inbound message arrived during this audit after the assignment; no subagent was used.

## G1 — normalization, finite moment, escaped tail and UI: ACCEPT

Write N=2^L, c=(M-1)^(1/s)>0 and x_L=c N^(1/s). Under uniform probability a single vertex has mass 1/N. Therefore the mean of 1+x_L 1_z is exactly 1+x_L/N=Z_L, with Z_L=1+c N^(1/s-1). Division by Z_L proves E q_L=1. Every value is strictly positive, and the minimum is 1/Z_L. Since s>1, the exponent 1/s-1 is negative and Z_L tends to one. Away from the vertex q_L tends to one, while the exceptional set has probability 1/N tending to zero. This is convergence in probability on the varying finite spaces, requiring no common probability-space coupling.

The exact sum has N-1 ordinary vertices and one exceptional vertex:

    E q_L^s = [1-1/N + N^(-1)(1+c N^(1/s))^s]/Z_L^s
            = [1-1/N + (N^(-1/s)+c)^s]/Z_L^s.

All powers are of positive numbers. The limit is 1+c^s=M. In particular, the extra term in the numerator is c^s, not c or c^s/N. For fixed K>1 the ordinary value 1/Z_L is below K, and the exceptional value (1+c N^(1/s))/Z_L tends to infinity. Eventually the tail consists of precisely the exceptional vertex. Thus its critical-power moment is (N^(-1/s)+c)^s/Z_L^s, which tends to c^s=M-1>0.

For every fixed K>1, the supremum over all L is at least this positive limit. Taking K to infinity after that supremum cannot yield zero. Thresholds q_L>K are the same as q_L^s>K^s, so this is exactly failure of UI of the critical powers, not merely divergence of pointwise maxima. The convergence-in-probability statement does not imply moment convergence to one without UI; here its failure is quantified. None of these arguments uses a dimension-dependent cutoff in place of a fixed K.

## G2 — floor, norm budget and arbitrary large M: ACCEPT

The floor 1/Z_L tends to one, so for any specified b<1 it is eventually at least b. The moments converge to M, and B^s>M by the strict hypothesis; hence E q_L^s<=B^s eventually. These are eventual statements for all L beyond a common finite index, even if no monotonicity of the moment sequence is assumed. Taking a maximum of the finitely many required indices, including the gap index in G5, gives the advertised L0.

For 1<=L<L0 put r_L=1. These prefix densities have mean one, floor one, Ls norm one and gap 1-rho. Because M>1 and B>M^(1/s), their norm is strictly below B. For L>=L0 retain q_L, so all constraints hold for every L. Altering finitely many dimensions does not change either moment limit, the fixed-K tail limit, or the limiting gap. UI still fails because a finite prefix cannot remove the positive tail limit along arbitrarily large L.

The constant c may be as large as any finite M requires. The argument only enlarges L0. It does not use the below-threshold stability theorem299, and it works for M>2 without modification. The quantifier is a separately constructed sequence for each fixed tuple (rho,M,B,b); it is not a single L0 uniform over unbounded M, b approaching one, vanishing budget slack, or rho approaching an endpoint. Strict budget slack is used exactly where needed. No assertion for B=M^(1/s) is inferred.

## G3 — multiplicity and the probability-normalized rank-one factor: ACCEPT

For A=M_sqrt(q_L) Q with Q=P_sqrt(rho), AA*=T_q and A*A=Q M_q Q=S_L. Both matrices are square of the same dimension. The squared singular values prove equality of the full ordered spectra with multiplicities, including any zero values; it is not merely equality of top norms. Here positivity of q and invertibility of Q actually make both positive definite, but the square-matrix argument needs no such strengthening. It does not identify Perron eigenvectors or their measures.

Let e_z=sqrt(N)1_z. In the probability inner product its norm is one and <e_z,f>=f(z)/sqrt(N). Hence e_z<e_z,f>=1_z f(z), exactly the multiplication projection M_{1_z}. This step removes the most plausible missing-N error. It follows that Q M_{1_z} Q is |Qe_z><Qe_z| and has norm ||Qe_z||2^2.

Since Q^2=P_rho, that squared norm is <e_z,P_rho e_z>. Evaluating it explicitly gives (1/N) sqrt(N) sqrt(N) P_rho(z,z)=P_rho(z,z). Each independent coordinate stays at its current sign with probability (1+rho)/2. Thus the exact rank-one norm is ((1+rho)/2)^L. It is neither that quantity divided by N nor multiplied by N. The amplitude outside this rank-one operator remains c N^(1/s), as in equation (5).

## G4 — perturbation size and strict contraction over the whole interval: ACCEPT

Subtracting P_rho from the exact formula for S_L gives

    S_L-P_rho = [-c N^(1/s-1) P_rho
                  + c N^(1/s) Q M_{1_z} Q]/Z_L.

The normalization correction has a minus sign. Bounding the two terms separately in operator norm is valid and need not be sharp. Since ||P_rho||=1 and G3 gives the other norm, this yields exactly

    ||S_L-P_rho|| <= [c d_rho^L + c a_rho^L]/Z_L,
    d_rho=2^(-(1-1/s)),
    a_rho=2^(1/s)(1+rho)/2.

The critical identity 1-1/s=2rho/(1+rho) gives the displayed a_rho=(1+rho)/2^(2rho/(1+rho)). In particular d_rho belongs to (0,1).

To check the less immediate a_rho inequality without numerical sampling, let f(t)=t log t. Its second derivative is 1/t>0 on [1,2], so its graph is strictly below the secant between t=1 and t=2 at each interior point. At t=1+rho this says (1+rho)log(1+rho)<2rho log2. Dividing by 1+rho and exponentiating proves a_rho<1 for every 0<rho<1. Positivity is immediate. The inequality becomes an equality at the excluded endpoints, so no endpoint-uniform rate is justified.

Both geometric terms tend to zero for each fixed rho and finite c, and Z_L>=1. The comparison is within the L-dimensional cube at each L; no subtraction of operators on different Hilbert spaces occurs. The candidate's explicit perturbation bound and the convenient larger bound c(d_rho^L+a_rho^L) are both correct.

## G5 — actual second eigenvalue, normalization and all-dimension gap: ACCEPT

The Walsh diagonalization of P_rho gives eigenvalues rho^|S|. For every L>=1 the first eigenvalue is 1 and the second is rho. When L>1 the second value has multiplicity L, which does not invalidate ordered-eigenvalue perturbation bounds. The min-max variational principle shifts every ordered eigenvalue by at most the norm perturbation, because it shifts every unit-vector Rayleigh quotient by at most that amount on every subspace. Applying it in both directions to S_L and P_rho proves the two inequalities in (8), including L=1.

It follows that lambda1(S_L)->1 and lambda2(S_L)->rho. Isospectrality in G3 transfers this to the actual full T_q, not a two-dimensional compression or a trial-vector surrogate. Testing S_L on the unit constant vector gives <1,S_L1>=<Q1,q_L Q1>=E q_L=1, so lambda1>=1 in every dimension. This lower bound justifies division without any eventual-denominator caveat.

Subtracting rho from the normalized second eigenvalue gives

    |lambda2/lambda1-rho|
      = |lambda2-rho + rho(1-lambda1)|/lambda1
      <= (1+rho) delta_L.

The numerator uses the perturbation estimate for both eigenvalues. Therefore gap tends to 1-rho. Choose L0 also such that c(d_rho^L+a_rho^L)<=(1-rho)/(2(1+rho)) for all L>=L0. Then gap>=1-rho-(1+rho)delta_L>=(1-rho)/2 throughout that tail. The prefix r=1 has the larger gap 1-rho. This proves the claimed explicit positive infimum over all L. It does not merely use that every finite positive matrix has some positive gap. Perron simplicity is consistent with the argument but alone would not establish its uniformity.

## G6 — comparison with296/299/300 and primary operator-tail theory: ACCEPT

The full copied source296 was read. Its two antipodal spikes have diagonal amplitude scale 2^(L/s)((1+rho)/2)^L and require 1<s<s_point=log2/log(2/(1+rho)) for that scale to grow. Source301 uses the same scale at s=s_c, where G4 proves it decays. Equivalently, a_rho<1 says s_c>s_point. Thus its comparison identifies the correct exponent regime and does not negate the earlier two-spike obstruction. The one-spike argument controls the whole transformed operator directly. No marginal-matching conclusion is imported from an unrelated construction.

The retained exact source299 says that every density below B*=2^(1/s) has a lower gap bound, while at and above B* there exist collapsing families. It does not say that every family above B* collapses. Stable examples with arbitrarily large M in301 coexist with those adverse examples. The nonnecessity proof itself never calls theorem299; that theorem is comparison context only.

The exact source300 states a sufficient critical-tail cutoff and a sufficient UI consequence, expressly without necessity. In301, for each fixed K>1 a nonzero amount M-1 escapes. Hence the critical powers fail UI while the actual gaps remain uniformly positive. This disproves a necessity upgrade, not theorem300. It also does not convert mere bounded critical moments into a sufficient condition: the negative family299 remains intact. If M is very close to one, the fixed-cutoff small-tail hypothesis of300 can be weaker than UI;301 claims failure of UI, not failure of every possible sufficient cutoff hypothesis.

[Wang, Criteria of Spectral Gap for Markov Operators, arXiv:1305.4460v6](https://arxiv.org/pdf/1305.4460v6), abstract, introduction and Theorem1.1 were checked again. The theorem concerns an ergodic invariant Markov operator, its symmetrization and a tail functional optimized over unit L2 inputs. Its operator UI definition concerns output tails. These objects are not the scalar base-measure density moments used here. Its fixed-operator characterization does not equate family-uniform density UI with family-uniform normalized gaps.

For clarity of the measure issue, with unit positive Perron vector phi the Markov transform is f -> T(phi f)/(lambda1 phi), invariant under phi^2 times the uniform measure. In general this is not the uniform measure or r times that measure. Spectral equivalence and normalization do not silently identify their tail functionals. The new example does not contradict or extend Wang's equivalence by changing its meaning.

The construction is a direct elementary application of a rare point spike, Gram isospectrality, norm perturbation and a moment calculation. Those ingredients are classical. This targeted source reading does not establish an identical published combined example, but that absence supplies no originality evidence. Correctness is accepted; external priority is unresolved. Its defensible role is the grouped explanatory limit of300, as the candidate states, with no standalone-paper importance claim.

## Objections and scope limits preserved

1. The strict slack B>M^(1/s) remains an explicit hypothesis. No exact endpoint budget theorem is accepted.
2. rho is fixed in (0,1). The contraction factors approach one at excluded endpoints; no bound uniform in varying rho is shown.
3. The index L0 depends on the requested parameters. The finite prefix replacement is required for the stated universal all-L constraints; the unmodified q_L is not certified to obey them in small dimensions.
4. This is an existence example for every requested tuple, not stability of all densities with that moment budget. The worst-case negative examples296/299 are preserved.
5. Escaped base-density moment is not a necessary obstruction to a gap. It must not be conflated with the invariant-measure operator-tail criterion.
6. No exact priority, independent-provider/human validation, formal verification, numerical grade, new PDF, local dynamics, marginal-matching, physical mass gap or continuum/Yang–Mills progress follows.

No blocking mathematical defect was found. No gate was amended, and no earlier failed or partial result was reclassified. The verdict binds only the frozen source and body named above.

## Evidence, privacy and cleanup

The raw subjects, assignment, context and provenance are recorded in MANIFEST.json with raw SHA-256 and byte lengths. Git blobs were captured directly as bytes without text newline conversion. Existing rules and sources299/300 were read in the retained prior audit context and verified unchanged by blob/hash or git diff;301 and296 were read in this audit. The body is separately identified by its required normalized representation.

`PRIVATE-Wang-1305.4460v6.pdf` is a private reference copy of the previously downloaded primary PDF. It is **excluded from every prospective public bundle**, as recorded in PRIVATE-SOURCES.md and the manifest. Retaining its raw hash is not permission to redistribute the article. No third-party PDF was created or newly published.

Repository state, branch and PR body were not modified. Existing untracked `_drafts/` and `_tmp/` were left untouched. No disposable clone, worktree, runtime or service was created, so no audit cleanup is pending. The retained evidence directory is on D: as requested.
