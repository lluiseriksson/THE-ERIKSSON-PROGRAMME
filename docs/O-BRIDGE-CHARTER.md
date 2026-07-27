# O CHARTER — "The operator bridge: from Euclidean clustering to a
# transfer-operator spectral gap" (registered 2026-07-27, BEFORE fabrication)

Owner order (2026-07-27, in-session): open the O lane after the
measurement in `docs/O-BRIDGE-AUDIT-20260727.md`; this desk FABRICATES,
external audit follows (role split per Part I regime rule 4 — this desk
does not judge its own artefact).

All Part II hard rules bind: no `sorry`, no project axioms, no vacuous
weakening, oracle every headline, job-count witness after core
integration.  All C1–C6 lessons bind: charters and amendments in OWN
commits before the work they govern; explicit staging (never `git add -A`);
hash rows from `git show`, never worktree bytes; the tricotomy of labels;
no score claimed without its external verdict.

## COORDINATION (registered now — the non-interference contract)

Concurrent lanes, from the owner: (a) **hRpoly** (Codex, Balaban
covariance: FTC of the rectangular minimiser, Neumann expansion of
`(QCQ*)⁻¹`, layer transport, physical walks); (b) **Surface Theorem
Part I** (Codex, `ladder15/16/17` certification campaigns); (c) **B-2**
(the Euclidean regime gate) — OPEN and UNCLAIMED, not this lane.

This lane works in NEW modules only, under the new namespace
`YangMills/OS/**`.  It does NOT touch:

- `YangMills/RG/**` (the whole hRpoly lane, including every `Physical*`,
  `AppendixF*`, `Catalan*`, `BalabanCMP*`, `PhysicalPoincare*` module),
- `YangMills/ClayCore/**`, `YangMills/KP/**`, `YangMills/L*/**`,
- `papers/surface-*`, `scripts/` and anything under the Part I queue.

The only shared files it will ever edit are `YangMillsCore.lean` (one
import line) and `oracle_check.lean` (one appended block), and only at
integration time; if either collides with another desk's push, resolution
is a PURE-ADDITION merge preserving both desks' lines, rebase-first.
Fabrication happens in the isolated short-path clone
`C:\Users\lluis\AppData\Local\Temp\obridge`.

## What the audit established (inputs, verbatim pointers)

- Zero occurrences of transfer operator, reflection positivity, GNS,
  spectral gap or physical spectrum in the 302 `.lean` files under
  `YangMills/` at `origin/main`.
- The M3 terminal statement `lattice_mass_gap_of_clustering`
  (`YangMills/Paper/ClusteringToGap.lean`) concludes about a function
  `cov : ℕ → ℝ`, not about any operator.
- The two satellites that would supply the link have it open:
  `lean-os-positivity` builds no GNS quotient; `lean-transfer-matrix`
  carries `gibbsTwoPoint_eq` **sorried** as its own declared "T0 honesty
  gap".
- Therefore closing hRpoly and surviving B-2 would still not produce a
  mass gap.  Bridge O is structurally independent of Bridge E.

## Phases, judges, budgets

- **Phase O-1 (THE AUTONOMOUS THEOREM; first fabrication).**
  New module `YangMills/OS/TransferGap.lean`:
  (i) `VacuumTransfer T Ω` — symmetric operator, unit vacuum, `T Ω = Ω`;
  `projectedTransfer T Ω = T − |Ω⟩⟨Ω|`; `connCorr` = the connected
  two-point function;
  (ii) `clustering_iff_gap` — an **equivalence**: exponential clustering
  at every vector at rate `r` ⟺ `‖T − |Ω⟩⟨Ω|‖ ≤ r`.  Stated as an
  operator-norm bound, deliberately NOT as `∃ gap > 0, …` (the shape of
  the vacuous terminal theorem this repository's history contains);
  (iii) `gap_of_dense_clustering` — the dense-family version, which needs
  a uniformly quadratic constant, and the module docstring stating why
  the two versions are BOTH shipped (they delimit the frontier);
  (iv) `volumeUniform_gap` — one rate `r < 1` shared across a family of
  volumes gives one mass `m = −log r > 0`, uniformly;
  (v) NON-VACUITY: `exists_vacuumTransfer_gap` and
  `euclidean_two_dim_vacuumTransfer_gap` — inhabitants with STRICTLY
  positive gap AND `projectedTransfer T Ω ≠ 0`, so no statement is
  satisfied only by the degenerate one-dimensional instance.

  **JUDGE J-O-1** (pre-registered, all five, in order, stop at first
  failure):
  1. module builds green; `#print axioms` on every headline prints
     exactly `[propext, Classical.choice, Quot.sound]`; zero `sorry`;
  2. the headline is an `iff`, and its right-hand side is not derivable
     without the left (checked by exhibiting the non-vacuity witness with
     `projectedTransfer ≠ 0`);
  3. anti-gameability: the C6 counterexample re-run — show the structure
     is NOT dischargeable by a scalar/trivial instantiation, i.e. the
     witness has a nonzero fluctuation sector and `0 < r < 1` strictly;
  4. after core integration, the build job count increments over the
     recorded 8410 baseline;
  5. adversarial self-audit for vacuous weakening, written into the
     commit message.
  Value alone (pre-registered band, absolute scale, C5 = 6.00 anchor):
  **4.5–5.5** — a correct, non-trivial, but classical operator-theory
  brick whose novelty is mechanisation plus the frontier it locates.  It
  is NOT worth more than that and no paper will claim more for it alone.
  Budget: 3 attempts.

- **Phase O-2 (THE GATE; the research risk).**  The audit's sharp
  question, now stated exactly because O-1 states it:

  > Is there a family of gauge-invariant observables, total in the
  > fluctuation sector, whose clustering constants are uniformly
  > quadratic in the Hilbert norm?

  The repository's constants are support-dependent and exponentially so
  (`C·e^{#loopSupp·4d·K}`; `C_clust = Σₙ C_conn n^dim A₀ rⁿ`), while a
  total family needs unbounded supports.  Two admissible outcomes, both
  publishable, neither promised:
  (a) a construction — a total family with uniformly quadratic constants,
      hence the operator gap from estimates of the type already proved;
  (b) a machine-checked OBSTRUCTION — the exponential support-dependence
      is not slack, and Bridge O closes negatively: a THIRD WALL in the
      format of the Poincaré-wall paper.
  **JUDGE J-O-2**: external evaluator verdict on whichever branch closes.
  ONE-SIDEDNESS RULE (Addendum 501, binding here): a favourable
  computation on any finite family is NOT a gate proof; only an
  all-families argument closes (a), only a proved lower bound closes (b).
  Budget: 3 attempts, then honest report.

- **Phase O-3 (conditional on O-2(a)).**  A fully non-vacuous instance:
  pure `Z_N` lattice gauge theory at strong coupling, where the gauge
  group is finite, every integral is a finite sum, and the whole chain
  (RP → GNS → transfer operator → identification → gap) is finite-
  dimensional linear algebra.  Target: a volume-uniform mass gap with NO
  carried hypotheses, for a genuine gauge theory.
  PRESENTATION RULE, registered now: `Z_N` is **not** SU(N); no Clay
  claim, no continuum claim, and the mother's strong-coupling VU area law
  (2607.0005) is the formal antecedent to cite.
  **JUDGE J-O-3**: non-vacuity audit (the model is not the trivial group,
  the gap is strictly positive, the fluctuation sector is nonzero) plus
  external verdict.  Budget: unset until O-2 closes.

## Kill criteria (registered now)

- O-1 needs a new axiom, or its witness has `projectedTransfer = 0` ⇒
  stop, diagnose in a commit, re-register.
- O-2 closes on branch (b) ⇒ the operator route from THIS repository's
  clustering estimates is DEAD; the charter converts to the obstruction
  paper plus a handoff naming what a different estimate would have to
  provide.  No silent pivot to an adjacent theorem.
- O-2 exhausts its budget without either branch closing ⇒ honest report,
  O-3 is NOT attempted, and the lane publishes O-1 alone at its
  pre-registered 4.5–5.5 band or not at all — owner's call.
- Any statement found vacuous at audit ⇒ same-commit retraction.
- Any collision with the hRpoly or Surface lanes ⇒ this lane yields.

## Score ladder (pre-registered, absolute scale, C5 = 6.00 anchor)

O-1 alone 4.5–5.5.  O-1 + O-2 obstruction (third wall) 5.8–6.5.
O-1 + O-2 construction 6.0–6.8.  O-1 + O-2 + O-3 (`Z_N` end-to-end,
volume-uniform, zero hypotheses) 6.5–7.2, with a distinct and separately
checkable novelty claim ("first machine-checked mass gap of a lattice
gauge theory") that must be verified against the literature by the
external desk before it appears in any abstract.  Kill risk on O-2:
50–65% on record.  No number is claimed in any paper without its external
verdict.

## What this lane will never claim

Progress on the Clay problem; anything about the continuum limit;
anything about SU(N) beyond what a proved reduction transfers; and no
"mass gap" wording for any statement whose conclusion is the decay of a
real-valued function.
