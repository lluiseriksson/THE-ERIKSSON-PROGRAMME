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
