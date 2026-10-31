# Unit045: actual multidimensional comparison and exact next bridge

Candidate TorusMeanPoincare derives coordinate decomposition on G=(ZMod n)^D,
translation displacement bounded by n times the sum of coordinate-step norms,
and actual finite-group averaging. Squaring and finite Cauchy-Schwarz give

    sum_x ||f(x)-mean(f)||^2 <= D*n^2 sum_i sum_x ||f(x+e_i)-f(x)||^2.

V is any real normed vector space, n>0; even D=0 is included. No desired
comparison or spectral-gap certificate is assumed. Verification status comes
only from exact reproduction reports; this note is not a verification witness.
This is a classical finite-path estimate with a deliberately nonoptimal constant.

Primary sources: author-hosted Levin/Peres, Markov Chains and Mixing Times,
section13.4, https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf (consulted
unit044), and pinned Mathlib Cauchy-Schwarz source consulted this unit:
https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean
The scalar mechanism/quadratic scale are established background. No original
priority or independent review is claimed for this formal vector-valued utility.

## Remaining single quadratic-counterexample question

Reuse, rather than reprove, the actual equivalence in TorusPhysicalEmbedding.lean
(finBoxZModEquiv) and its wraparound transport finBoxZModEquiv_shift in
TorusPhysicalShift.lean. The latter sends x.shift i to e(x)+Pi.single i 1,
exactly torusUnit i. For A : PhysicalGaugeOneCochain D n Nc define the directional
mean mu_i=n^(-D)*sum_x A(x,i), construct the constant physical embedding, and
apply the torus inequality to each component after actual equivalence reindexing.

The actual componentwiseFlatGradientCLM (ComponentwiseFlatGradient.lean) has
index Fin D x PhysicalBond D n and value A(x.shift i,j)-A(x,j). Its norm is
precisely the double direction/site difference sum after Fintype.sum_prod_type.
Actual constant physical norm bookkeeping is already proved by
norm_sq_constantPhysicalGaugeOneCochain in PhysicalGaugeFlatPoincare.lean.

Prove actual mean-zero sum and the orthogonal decomposition in the real Hilbert
coordinate space, then obtain

    ||A||^2 <= D*n^2 ||componentwiseFlatGradientCLM A||^2
                  + n^D sum_i ||mu_i||^2.

Output can be PiLp2 over Fin D with values SUNLieCoord Nc: fixed dimension
D*(Nc^2-1). Repair weights D*n^2 and Phi_n(y)=n^D||y||^2 should give coefficient1.
The penalty constant varies with n and is not uniform1. The full physical
construction is unfinished until these actual reindexing and orthogonality
identities are verified. Do not count the present torus result as that endpoint.

Falsifier: shift-wrap/norm/cardinality mismatch or nonzero mean-zero zero-energy
field. After three units with no useful advance preserve failures and identify
the concrete obstruction or change route. No interacting/continuum Yang-Mills
consequence, no physical hypothesis removed. PR29 remains20/41,TermSource0.

Initial driver060 was rejected by the source-hash guard before Lean ran: a
global renumber replacement059->060 inadvertently altered the substring059 in
the actual source digest. Full rejection bundle retained. Driver061 fixes only
the expected hash and uses targeted path/label renumbering. Source theorem SHA
and acceptance guard are unchanged; both corrected driver digests were checked
against actual LF files before reconnecting. Prepared060b was not executed.

Compiler061 exposed coordinate cast and nested energy normalization obligations; both were made pointwise/explicit at9b0b8a4d. Compiler062 then rejected an ambiguous Pi.single fiber in the auxiliary equality. Explicit Fin D -> ZMod n type/modulus annotation atadc46998 fixes that term. Exact statements/guard unchanged; full original sources and patches retained. Prepared061b/062b not executed.
Compiler063 made explicit that single evaluation requires simplification, not definitional change. At d02530a5 the proof simplifies Pi.smul_apply and Pi.single_apply before the scalar cast. No theorem statement or oracle rule changed; prepared063b not executed.
Run064 is INCOMPLETE, not PASS or mathematical FAIL: its tab vanished during execution; reopening the exact Drive notebook recovered only output through lean-version. Session-management UI showed disconnected, with no final bundle/report. Partial output and UI preserved. Run065 repeats the identical d025 mathematical source, with a retained evidence tab. Prepared064b was not executed.
