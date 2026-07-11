# C1 CHARTER — "Machine-verified rooted-tree majorants for polymer expansions with holes"

Registered 2026-07-11, BEFORE the page (Part-I discipline applied to
a Part-II-territory paper; both rule-sets bind: no sorry, no project
axioms, no vacuous weakening, oracle every headline, judges before
pages, tricotomy, transcripts-when-committed).

## What the paper IS (honest scope, fixed now)

A self-contained, fully machine-verified quantitative theorem set for
polymer/cluster expansions with excluded regions (holes), built from
three pinned Lean endpoints (already proved, zero sorry at grep level,
oracle files present) plus ONE new certified-numerics companion:

- E1 `normalizedRootedChildFactorialTreeBound`: the Catalan/tree
  closure — normalized child-factorial mass of complete-graph
  spanning trees ≤ 4^n (the rooted-tree majorant).
- E2 `markedRootLeafGeometricBound`: marked-root leaf summation for
  the second Ursell expansion with holes — geometric bound with
  moment constant paid once at the root.
- E3 `targetPreservingWeightedTreeBound`: target-preserving orderwise
  bound (exp weight extracted only after the target union is used).
- NEW (this fabrication): the certified admissibility companion —
  an arb-certified table of (d, kappa_0) satisfying the smallness
  gate hCq: (3^d)^2 * e^{-kappa_0} * 2^{3^d+1} < 1, with the
  resulting moment/leaf constants enclosed (ball+boolean), plus
  NON-VACUITY witnesses: a concrete HoleFamily instance per table
  row satisfying every hypothesis of E2/E3 (the Part-II vacuity
  precedent makes this mandatory, not decorative).

NO importance is claimed beyond what is proved: this is expansion
TOOLING with machine constants. The YM programme is named as origin
substrate; no Clay-adjacent claim of any kind appears.

## Pre-registered judges (all must pass before submission-grade)

- J-C1-1 BUILD: `lake build MarkedRootedClosure` green on the pinned
  toolchain; the three endpoints' `#print axioms` show exactly
  [propext, Classical.choice, Quot.sound]; core job count recorded.
- J-C1-2 CERTIFIED COMPANION: arb transcript, pre-registered bands:
  d=2 admissible for kappa_0 >= 16 (predicted from ln(81^2*2^10) ≈
  15.72); d=3 admissible for kappa_0 >= 33 (ln(729^2*2^28) ≈ 32.60);
  each table row carries the enclosed constants and the boolean gate.
- J-C1-3 NON-VACUITY: for at least one (d, L) a concrete HoleFamily
  with nonempty, disjoint, edge-separated holes is EXHIBITED in Lean
  (instance term, not `∃`), satisfying E2/E3's hypotheses.
- J-C1-4 PAPER: TeX with tricotomy labels (exact = Lean theorems;
  certified = arb transcript; verified = any calibration numerics),
  dual-hash provenance for every artifact, honest title, and the
  standing rg-check discipline (no label above its witness).
- J-C1-5 AUDIT: one independent internal audit round (split roles)
  + Codex re-derivation of the admissibility arithmetic (premises
  audited against code, per the standing jurisprudence).

## Fallback (declared now)

If the endpoints do not build against the current core pin, the
measured failure is committed and the paper waits for the pin
reconciliation — no vendored copies, no axiom bridges, no weakening.

## AMENDMENT 1 (2026-07-11, post-recon, still before the page)

The committed recon (docs/REPO-RECON-2026-07-11.md) upgrades the
charter WITHOUT widening its honest scope:

- E1 UPGRADED: the EXACT identity
    Sum_{T in spanningTrees K_{n+1}} Prod_v (childCount_T v)!
      = n! * catalan(n)
  is proved unconditionally (rooted-tree-catalan-closure, committed
  axiom-oracle log + CI replay); the charter's 4^n bound becomes
  its corollary.  The paper's headline is the identity, not the
  bound - and the marked-root Ursell overcount sharpens by ~n^{3/2}.
- E2 UPGRADED: the discharged consumer
  appendixFHoleHsharpWeightedTreeMarkedRootSum_le_catalan is
  already written against mother namespaces; the MERGE (only risk:
  base-commit drift) joins J-C1-1, and the mother core's carried
  Catalan HYPOTHESIS is discharged by it - a named-hypothesis
  removal, the house's favourite currency.
- SIDE ARTIFACT declared: the Mathlib PlaneTree PR
  (mathlib-plane-tree-catalan) is submission-ready per its own
  compile+oracle log; it ships as the paper's standalone
  upstreaming companion.
- CROSS-PROGRAMME FLAG (outside C1 scope, queued for the owner):
  recon bridge 2 - ONE Bessel/Amos module would discharge the same
  named hypothesis at three sites INCLUDING the active Part-I
  paper's own conditional (E'<0 for beta <= 3.5 rides
  phi_step_of_recurrences); exact2d.py already computes certified
  enclosures of exactly those ratios, slack floor 2.5e-7 on
  [1,100]x[0.01,300] pre-registrable as judge.  C1 does NOT absorb
  it (scope discipline); it is the natural next item for EITHER
  programme.

## AMENDMENT 2 (2026-07-11, POST-RUN correction, transcript cited)

J-C1-2 first run (scripts/c1_admissibility_arb.py, sha256
f114fc4b..., transcript scripts/c1_admissibility_transcript.txt,
exit 0):

- REGISTERED BANDS HOLD: d=2 k0>=16 and d=3 k0>=33 pass hCq
  provably.  Certified row constants (k0=16: M in 1.0094221 ball,
  Lf 4.0757316, eps* 0.24535472; k0=33: M 1.0009125, Lf 4.0073035,
  eps* 0.24954436).
- REGISTERED PREDICTED CROSSOVERS DO NOT RE-DERIVE (measured):
  true k*(2) = 11.32592096 vs registered 15.72; true k*(3) =
  25.99979479 vs registered 32.60.  DIAGNOSIS: the charter's hand
  assembly wrote (3^d)^4 where the Lean gate carries (3^d)^2 -
  ghost-#23 class (constants computed, never assembled).  The
  BANDS stay as registered (true-but-not-sharp); the paper inks
  ONLY the certified values.  Edge display row: d=3, k0=26 passes
  by G = 0.99979 and the constants blow up (M ~ 4.9e3,
  eps* ~ 1.05e-8) - the certified illustration of gate sharpness.
- Run-1 note (honesty): the first execution printed the identical
  table then died at the crossover-audit print on an
  AttributeError (arb has no .abs(); builtin abs() is the API) -
  a tooling typo, fixed and rerun to exit 0; no mathematical
  content changed between runs.

## AMENDMENT 3 (2026-07-11, third-desk re-derivation logged)

J-C1-5's Codex half is DONE (round 1, relay-class, never ink):
independent decimal-80 re-derivation of all four audited rows and
both crossovers agrees with the committed transcript to >= 7
significant digits, every exact value inside its printed ball;
script sha256 independently reproduced; rem:crossover confirmed
arithmetically.  ONE overclaim sustained and applied in paper v2:
eps* = 1/Lambda was presented as "certified activity radius for
the endpoints" while the Lean endpoints prove coefficient bounds
M Lambda^n only - the activity-series passage is paper-level
algebra conditional on the eps^n structure and the paper now says
so (tricotomy status spelled out); band booleans re-scoped to the
two registered endpoints with the exact monotonicity extension
noted; strict-gate wording adopted.  The split-roles INTERNAL
audit round of J-C1-5 remains OPEN (a different session must run
it against the judges).

## AMENDMENT 4 (2026-07-12, RELEASE c1-v1.0 - judges closed, audit registry)

JUDGES:
- J-C1-1 BUILD: PASSED. lake build MarkedRootedClosure exit 0,
  8244 jobs, pinned toolchain; integration commit 4f95a5ad; oracle
  [propext, Classical.choice, Quot.sound] on ALL SEVEN theorems
  (5 endpoints + 2 non-vacuity), log scripts/c1_oracle_output.txt.
  Two paths to green recorded honestly: cold-cache infrastructure
  rebuild (no warm .lake existed on this machine - CCleaner purges
  Temp; deps prefetched depth-1 at pinned revs, ProofWidgets needs
  its release tag, mathlib oleans via lake exe cache get), then two
  measured NonVacuity failures (decide maxRecDepth on
  Finset-of-function kernel evaluation; missing Decidable instance
  for the def noEdgesBetweenHoles) plus two API slips
  (Finset.not_mem_singleton absent in pin; gcongr closing via
  assumption) - fixed with structured term proofs, diagnosis in the
  integration commit message.
- J-C1-2 CERTIFIED: PASSED (Amendment 2) + reproduction witness
  committed (rerun byte-identical, sha comparison log).
- J-C1-3 NON-VACUITY: PASSED. Concrete HoleFamily d=2 L=8, two
  singleton holes at sup-distance 4, strictly positive weight
  e^{-32(rho+1)}, both hypothesis sets instantiated, oracle clean.
- J-C1-4 PAPER: PASSED. v6 = c1-v1.0: ZERO slots, tricotomy sweep
  complete, readable definitions, proof architecture, related work
  (10 refs verified online), quantitative example, reproducibility
  section with theorem-to-artifact map and release facts, explicit
  limitations. Title corrected Machine-VERIFIED -> Machine-CHECKED
  (reserved-word discipline; supersedes the charter name).
- J-C1-5 AUDIT: PASSED (five roles, all documented):
  (1) Codex re-derivation (Amendment 3): numbers PASS, 1 overclaim
      sustained -> fixed v2.
  (2) Numeric auditor (independent session, mpmath dps=50, third
      library): PASS ZERO findings; worst deviation 4.5e-8 rel =
      printing precision; paper table digit-perfect; hCq chain
      margins x1.114 / x96.2.
  (3) Mathematical referee (independent session): all definitions,
      five statements, constants, table, witnesses, pin-drift audit
      VERIFIED against source; 6 discrepancies (D1 swapped
      gate-factor attribution in Sec 4.2 prose, D2 missing u>=0,
      D3 example wording, D4 corollary provenance, D5 L>=3 nit,
      D6 any-tuple gloss) - ALL FIXED in v5. Bonus verifications:
      Penrose passage IS formalized upstream
      (abs_ursell_le_card_spanningTrees); superadditivity lemma
      located and named; referee independently re-ran the arb
      script (byte-identical).
  (4) Hostile editor (independent session): 25 findings, 5 blocking
      (false submitted-to-Mathlib claim, tricotomy breaches incl
      title, unwitnessed reproduction claim, thm:target hypothesis
      gap, reserved-word collisions) - ALL 25 addressed in v5.
  (5) Formal+reproducibility auditor: verdict pending at tag time
      (launched on the release tree; report will be appended as
      Amendment 5). The tag was placed before this last report by
      sequencing necessity; any finding it sustains will be fixed
      in a post-tag commit and noted, never by moving the tag.

RELEASE: tag c1-v1.0 = commit a9a440fe (paper tex+pdf v6, changelog,
witnesses); Lean integration 4f95a5ad. Registered-name note: the
charter title said "Machine-verified"; the released title is
"Machine-checked" (hostile-editor finding 3, reserved-word rule).

LIMITATIONS carried into the release (explicit, also in CHANGELOG):
signed-coefficient passage upstream; activity-series algebra
paper-level; polynomial-only gain; witness = satisfiability not
sharpness; one cold-clone build this session (no second-hardware
replay); PlaneTree PR prepared, NOT opened.

## AMENDMENT 5 (2026-07-12, post-tag: formal+repro audit CLOSED)

Role (5) of J-C1-5 delivered PASS 7/7 on the release tree at
c1-v1.0: (1) oracle independently re-run, seven theorems, exact
axiom lists, names seven-for-seven vs paper; (2) committed oracle
log byte-identical to the independent rerun (blob sha bdb40f62...;
benign CRLF worktree-checkout artifact flagged - compare against
git show <rev>:path on this box, not the worktree); (3) integration
commit contents and tag target verified (c1-v1.0 -> a9a440fe);
(4) witness weight strictly positive BY DEFINITION (exp of a real),
zero sorry/axiom matches in the module; (5) arb transcript
reproduced byte-identically a THIRD time, all hashes re-derived;
(6) command-sequence premises verified, cold-clone build fact
explicitly scoped out and matching the paper's limitations ink;
(7) tex+pdf same commit. NO post-tag fixes required. The audit
round of J-C1-5 is CLOSED with five documented roles.

## AMENDMENT 6 (2026-07-12, documentation patch c1-v1.0.1)

External tag-level review (8.55/10, "apto para preprint") sustained
three ARCHIVAL gaps, no mathematical findings; reviewer verified tag
contents, source, pins, hashes, PDF, and independently computed the
LF-blob hash 46C6...; explicitly instructed: do not move c1-v1.0, do
not reconstruct logs - patch only with originals if they exist.
All three verified at this desk before applying:
(1) BUILD LOGS: originals existed in the session scratchpad; the
    repo *.log gitignore rule had silently excluded them from every
    commit.  All three raw run transcripts committed unmodified
    (.log -> .txt rename only): run1 FAIL (cold cone, 8241 green +
    NonVacuity decide failures), run2 FAIL (pin API), run3 GREEN
    (8244 jobs exit 0, sha 981AB56C...).
(2) DUAL HASH: v1 witness hashes were CRLF-worktree representations
    (0319...); canonical LF-blob is 46C6C171... - both re-derived
    here, matching the reviewer.  COMPARISON_v2 declares both; the
    house dual-hash rule (provenance round 5) should have been
    applied to the witness from the start - noted as the lesson.
(3) EXPEDIENT IN TAG: Amendments 4-5 postdated c1-v1.0; the patch
    tag c1-v1.0.1 contains the full audit expedient plus
    papers/c1-rooted-tree-majorants/RELEASE-MANIFEST.md
    (integration commit / manuscript commit / tags / canonical
    hashes) and a paper Reproducibility paragraph pointing at all
    of it (tex+pdf same commit).
c1-v1.0 remains the mathematical artifact; c1-v1.0.1 is the
self-sufficient audit expedient.  Verdict adopted: preprint-ready;
journal submission decision remains the owner's.

## AMENDMENT 7 (2026-07-12, hash-labeling micro-patch c1-v1.0.2)

External verification of c1-v1.0.1 (8.70/10, verdict unchanged:
preprint-ready) reproduced every committed hash and sustained ONE
residual labeling gap, zero mathematical/formal/numerical findings:
the manifest's run3 hash 981AB56C... was the CRLF capture
representation while the tag ships the LF blob (5053A86E...).
c1-v1.0.2 appends to the manifest: dual LF/CRLF hashes for ALL
THREE build logs, the patch's own tex/pdf blob hashes (E81867B1 /
FC90104D, reviewer-matching), and the explicit sentence that Git
normalized the logs CRLF->LF at blob formation ("unmodified" =
content not reconstructed, not binary identity across EOL
normalization).  No paper recompile - tex/pdf blobs identical
across v1.0.1 and v1.0.2 by construction.  Neither prior tag moves.

## AMENDMENT 8 (2026-07-12, FABRICATION CLOSED)

Final external verdict on c1-v1.0.2: 8.70/10, apt for preprint
circulation, ZERO open findings, all hash tables reproduced by the
reviewer from the tag itself, tag chain confirmed well-separated
(v1.0 mathematics / v1.0.1 audit expedient / v1.0.2 provenance
closure), cosmetic apostrophe residue in auxiliary tag documents
acknowledged by both desks as not tag-worthy.  Reviewer recommends
NO further documentary patches.  The C1 fabrication arc is CLOSED
at this desk.  Remaining steps are the owner's alone: preprint
circulation / journal submission, and opening the prepared
PlaneTree Mathlib PR.  Any future work on C1 (post-referee
revisions, consuming markedRootCatalanBound upstream where the 4^n
budget is paid) starts a NEW registered arc against this charter.
