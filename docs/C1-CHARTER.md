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
  axiom-oracle log + CI replay); the charter''s 4^n bound becomes
  its corollary.  The paper''s headline is the identity, not the
  bound - and the marked-root Ursell overcount sharpens by ~n^{3/2}.
- E2 UPGRADED: the discharged consumer
  appendixFHoleHsharpWeightedTreeMarkedRootSum_le_catalan is
  already written against mother namespaces; the MERGE (only risk:
  base-commit drift) joins J-C1-1, and the mother core''s carried
  Catalan HYPOTHESIS is discharged by it - a named-hypothesis
  removal, the house''s favourite currency.
- SIDE ARTIFACT declared: the Mathlib PlaneTree PR
  (mathlib-plane-tree-catalan) is submission-ready per its own
  compile+oracle log; it ships as the paper''s standalone
  upstreaming companion.
- CROSS-PROGRAMME FLAG (outside C1 scope, queued for the owner):
  recon bridge 2 - ONE Bessel/Amos module would discharge the same
  named hypothesis at three sites INCLUDING the active Part-I
  paper''s own conditional (E''<0 for beta <= 3.5 rides
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
  25.99979479 vs registered 32.60.  DIAGNOSIS: the charter''s hand
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

J-C1-5''s Codex half is DONE (round 1, relay-class, never ink):
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
