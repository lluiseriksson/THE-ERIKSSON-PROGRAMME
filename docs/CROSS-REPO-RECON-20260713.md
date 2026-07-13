# CROSS-REPO RECON UPDATE — 2026-07-13 (delta over REPO-RECON-2026-07-11.md)

Desk: reconnaissance update (survey; no fabrication, no audit role claimed).
Method: four parallel web-recon passes over the 17 satellite repos (GitHub
pages + raw READMEs + spot-fetched source files), cross-checked against the
LOCAL mother clone by grepping for satellite theorem names.  The 2026-07-11
recon (`docs/REPO-RECON-2026-07-11.md`) remains the per-repo inventory of
record; THIS file records only what CHANGED, what its five bridges' status
is now, the viXra-catalog citation map, and the alignment with the frontier
as it stands after Addenda 469-480 (P4-CT complete, C6 charter registered).
Honesty rule of the house applies throughout: importance is not inherited
by thematic proximity; only a proved reduction transfers it.

## 1. Bridge status update (the 07-11 recon's Part B, re-judged)

- **Bridge 1 (Catalan closure -> mother Appendix-F): EXECUTED/ABSORBED.**
  `sum_prod_rootedChildCount_factorial_eq`,
  `rootedChildFactorialCatalanIdentity_holds`, and the discharged adapter
  live in the mother (`YangMills/KP/RootedCatalanIdentityProof.lean`,
  `RootedCatalanBridge.lean`, `RootedCatalanExact.lean`,
  `PlaneTreeCatalan.lean`; ledger Addendum 445).  The satellite repos
  (rooted-tree-catalan-closure, lean-rooted-tree-polymer-expansion) are
  ARCHIVED publication artifacts; nothing left to import.
  REMAINING CHEAP ACTION (social, owner-gated): the Mathlib PR of
  `PlaneTree.card_treesOfNumNodesEq_succ` is PREPARED in
  mathlib-plane-tree-catalan (docs/PR1_DESCRIPTION.md + committed compile
  oracle) but was NEVER OPENED.  Nothing by this author is actually in
  Mathlib yet.
- **Bridge 2 (one Bessel/Amos module, three consumers): SUPERSEDED BY
  C3/C4.**  `amosBound_holds` (C3) and `amosBoundReal_holds` +
  `besselIReal_natCast` (C4) are mother theorems now.  The remaining
  consumers are wiring, not mathematics: (i) the Part-I phi-lemma
  (`phi_step_of_recurrences`) still CARRIES `hAmos` as a hypothesis — it
  can now be discharged BY THEOREM through the C4 identification (owner
  priority decides when, it is Part-I lane); (ii)
  lean-transfer-matrix/FHBessel's `unit_step_of_recurrence_and_amos`
  likewise.  2D string-tension positivity in lean-2d-yang-mills follows
  the same way if ever wanted.
- **Bridge 3 (Ising vertical slice, OS -> transfer -> gap): OPEN, and its
  VALUE ROSE** — it is now the toy twin of the C6 correlator bridge.  The
  satellite frontier names the exact same honesty gap C6 attacks:
  lean-transfer-matrix's `gibbsTwoPoint_eq` (Gibbs-measure two-point ==
  transfer-operator correlation) is SORRIED on a frontier branch and
  labeled a "T0 honesty gap" there.  Reference material for the C6 desk
  (its lane, not this one): `TransferOperatorInterface`,
  `HasStrictSpectralGap`, `isingInterface` (the one hypothesis-free
  instance FOUND IN THIS SWEEP of the 18 inspected heads; exact gap
  `-log tanh beta` — valid for `beta > 0`; at `beta = 0` the ratio
  vanishes and no finite positive rate exists), and lean-os-positivity's
  `HasOperatorMassGap` with proved `.pos`/`.quadratic_lower_bound`.
- **Bridge 4 (coercivity screens): OPEN, value unchanged, new consumer.**
  hausdorff-certificates' exact-rational LDL^T decide-or-falsify backend +
  the Hankel support test (`K >= cI  <=>  supp in [0, theta]`,
  `theta = x0/(c+x0)`; Lean half in riemann-resolvent-programme) is the
  right FALSIFIER HARNESS for the volume-uniformity question: screen
  CP(L) growth of the flat shell numerically on small volumes to
  quantify the proved `CP >= L^{d-2}` collapse before spending Lean
  effort.  Caveat: mpmath intervals, below the Part-I arb standard —
  usable as design/falsifier only, not as a certified transcript source.
- **Bridge 5 (vendor the three-infinities lemma): LIKELY MOOT — VERIFY
  BEFORE VENDORING.**  The mother now has its own
  `YangMills/RG/TripleInfinityClosure.lean`
  (`tripleInfluence_le_of_geometric_leaf_scale_budget`, Addendum 453)
  covering the same order/geometry/scale collapse in ℝ with explicit
  budgets.  The satellite version (physmath-lean-lemmas,
  `rootedTripleInfinity_closure_le`) is in ℝ≥0∞ on a DIFFERENT pin
  (v4.31.0).  The 07-11 pre-registered judge ("at least one existing
  mother proof strictly shortens, else vendoring fails") would likely
  FAIL now; do not vendor without running that judge.

## 2. New finding — provenance of the P4-CT ladder

`aqft-split-inclusion-series` contains
`verification/0064/brick_P45_combes_thomas.md`: a design note WRITTEN
AGAINST THE MOTHER's hRpoly brick P4.5 stating the target
`physicalCovarianceKernel_expDecay` and a three-lemma Combes-Thomas chain
(diagonal conjugation `M_theta` with defect `<= (e^{thetaR}-1)S`; Neumann
inversion when defect < coercivity; kernel extraction).  The P4-CT ladder
closed this week (Addenda 469-477) implements that blueprint's SHAPE with
one substantive improvement: the inversion step is the COERCIVE route
(`covarianceOfIsCoerciveCLM` at the theta-budget) rather than Neumann,
which is what makes Laplacian-type operators reachable.  PROVENANCE
OBLIGATION: any CT-brick paper must cite the design note (and the classical
source Combes-Thomas CMP 34, 1973, already cited in the module headers).

## 3. What the satellites do NOT have (absences: NOT FOUND in the
inspected heads — auditable claim, not a totality claim)

- P4-ADJ (SU(N) adjoint on su(N), `finrank = N^2-1`, `Ad(g)X = gXg^{-1}`):
  not found in any inspected head — Addendum 477's registration stands as
  genuinely new work.  Nearest substrate: lean-2d-yang-mills' proved SU(2)
  character/Haar/3-sphere stack (fundamental rep only).
- Volume-uniform Poincare/spectral constants: nowhere (the satellite
  uniformity predicate `HasUniformExponentialClustering` carries
  existential constants, flagged in its own frontier).
- OS reconstruction: lean-os-positivity's GNS quotient is SORRIED on
  frontier/M1; what IS proved there (pairing-form calculus, RP <=> PSD
  bond kernels, Ising + 1D-Gaussian-chain RP instances) is real and will
  matter at M4/M5 — not before.
- Gaussian free field with `(-Delta+m^2)^{-1}` decay: lean-gaussian-field
  M3 not started; the mother's own Gaussian substrate is ahead.
- Flow route components (unitary bridge, flow-sliced transport, Jacobian,
  marginal extraction): none in lean-ym-flow; only proved piece there is
  the discrete-heat maximum-principle/mass-conservation toolbox.
- Connes-Kreimer: M0 polynomial algebra only; no coproduct/antipode/BPHZ.
  No consumer in the mother; remains a rejected bridge.
- lean-zero-free-regions' M0 (KP => nonvanishing, domination transport,
  fugacity-section analyticity): ABSORBED — the mother's
  `YangMills.KP.ActivityDomain` (the "first upstreamed satellite
  consumer", CURRENT-STATE) covers it.

## 4. viXra catalog -> citation map for the live lanes

Standing rule: these are SAME-AUTHOR PRIOR-ART citations ("conditional,
paper-level" unless stated); none is a proof source without the
link-by-link audit CLAUDE.md prescribes.  The 2602 series is precisely
the "claimed bridge" corpus that instruction (c) says must be audited
link-by-link before any importance transfers.

- **C6 correlator bridge (other desk)** — categories separated per the
  4316168a dictamen: DIRECT MATHEMATICAL ANTECEDENT (must cite):
  2602.0088 (exponential clustering + gap via Balaban RG and MULTISCALE
  CORRELATOR DECOUPLING — its own abstract announces the covIR+covUV-type
  identity).  PROGRAMMATIC CONTEXT (cite when its checklist/framing is
  used): 2602.0091.  APPARATUS (cite ONLY when its audit/navigation
  claims are actually consumed — imposing it on every C6 paper would be
  apparatus self-citation, not content): 2602.0096/2602.0117.
  DIRECT PROVENANCE OBLIGATION for the CT brick specifically: the P4.5
  design note (section 2) + Combes-Thomas CMP 34.
- **Volume-uniform Poincare (this lane's wall)**: paper-side antecedents
  2602.0040 (uniform Poincare via multiscale martingale decomposition),
  2602.0041 (uniform LSI + gap), 2602.0089 (spectral gap + thermodynamic
  limit via LSI + complete analyticity), and the windowed LSI series
  2602.0051-0057.  The martingale-decomposition ROUTE of 2602.0040 is a
  candidate formalization strategy for escaping the `CP >= L^{d-2}`
  collapse; treat as source material under SOURCE-CLAIM-AUDIT discipline,
  not as established.
- **hRpoly/UV lane (this lane)**: 2602.0069 (Balaban-Dimock structural
  package), 2602.0077 + 2602.0085 (UV stability), 2602.0070/0072/0073
  (influence bounds, RG-Cauchy).
- **Released formal satellites (cite by id, delivered 2026-07-12/13)**:
  C1 = 2607.0025 (rooted-tree majorants), Catalan identity = 2607.0001,
  VU area law = 2607.0005, C2 = 2607.0033, C3 = 2607.0032,
  C4 = 2607.0030 (own id, on record), C5 paper in flight per its lane.
- **OS/axioms (future M4/M5)**: 2602.0092 (rotational symmetry +
  Wightman), 2602.0084 (almost RP via Gaussian localization), and
  2512.0060 [AQFT clustering/recovery] as adjacent-method prior art.
- **Off-lane (no proved reduction, do not cite into YM work)**: the
  quantum-maintenance/recoverability series (2512.*, 2601.*, 2607.0028/
  0029/0031), the Riemann repos (owner's own curation record already
  discards the RH<->YM link), heat-kernel/induced-gravity items.

## 5. Actionable queue distilled (respecting lane ownership)

1. (This desk, cheap, next) P4-ADJ ladder brick 1: `finrank su(Nc) =
   Nc^2 - 1` + the trace inner product on traceless anti-Hermitian
   matrices — substrate for the true adjoint model; no satellite help.
2. (This desk, falsifier, before any volume-uniformity fabrication)
   numeric CP(L) screen of the flat shell via the hausdorff-certificates
   pattern (exact-rational LDL^T on small volumes) to size the
   `CP >= L^{d-2}` obstruction and test whether any rescaling of the
   block map restores uniformity.  Registered as design-only unless a
   protocol is pre-registered.
3. (C6 desk, reference forwarded) lean-transfer-matrix vocabulary +
   sorried `gibbsTwoPoint_eq` as the toy twin of the correlator
   identification; 2602.0088 as the mandatory prior-art citation.
4. (Owner, social) open the prepared Mathlib PR
   (`PlaneTree.card_treesOfNumNodesEq_succ`) — zero mathematical risk,
   the only step to a first actual Mathlib contribution.
5. (Part-I lane, when owner resumes it) discharge the phi-lemma's
   `hAmos` from C4's `amosBoundReal_holds` + identification — removes
   the last classical-Bessel hypothesis from the E'-relay's Lean core.

## 6. Coordination note (owner update, 2026-07-13, post-recon)

The owner confirms ACTIVE parallel desks beyond the two known here:
lean-2d-yang-mills is being worked by its own desk toward the EXACT 2D
SU(2) heat-kernel/Migdal chain (canonical Haar equality paper already
produced; registered ladder: general Weyl -> full Haar orthogonality ->
concrete heat-kernel convolution -> nontrivial Migdal move -> exact
simple-loop law), with the explicit presentation rule that the mother's
strong-coupling VU area law (2607.0005) is the FORMAL ANTECEDENT to cite
and the exact 2D law is a DIFFERENT result in regime, mechanism, and
conclusion — no "first machine-checked area law" claim.  Section 1's
characterization of that repo ("conditional packages") is the head
snapshot; an active lane sits behind it.  Lane map now: (a) C6 bridge
desk (isolated clone), (b) THIS desk = hRpoly/P4 lane, (c) Surface
Part-I desk (Codex; K2/G3/G4 certification campaigns in flight), (d)
2D-exact desk on lean-2d-yang-mills.  No cross-lane fabrication.

*End of update.  The 2026-07-11 inventory remains authoritative for
per-repo detail.*
