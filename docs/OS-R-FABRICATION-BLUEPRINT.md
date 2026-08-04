# OS-R FABRICATION BLUEPRINT — OSReconstructionUniform.lean

Companion to docs/OS-RECONSTRUCTION-CHARTER.md.  Written 2026-08-04 at
design time, grounded in the sources (all names below verified to exist
at `c76b79050`).  This is the fabrication input; it licenses nothing by
itself (the plane judges do).

## Imports and setting

```
import YangMills.OS.SpatialReconstruction   -- pulls SpatialOS, SpatialGibbs
import YangMills.OS.DobrushinCorollary      -- dobrushin_ising_uniform_gap, sliceW
import YangMills.OS.DobrushinTilt           -- tiltKernel(_apply), symWeighted
import YangMills.OS.DobrushinTransport      -- opOf, vacOf
import YangMills.OS.TransferGap             -- VacuumTransfer, projectedTransfer
```

Slice type throughout: `Conf L := Fin (L+1) → Fin 2` (D-6's corollary
type).  OS-lane theorems quantify over their own `L`; instantiate their
`L := L+1` (their slices are `Fin L → Fin 2`).  Weight `w := sliceW γ L`
(positive by `sliceW_pos`).  Temporal kernel: whatever `bondForm`
carries — CHECK at fabrication that it is `spatialKernel β` (SpatialGibbs)
or prove pointwise equality once and rewrite.  `symWeighted w β σ τ`
should be `√(w σ) * spatialKernel β σ τ * √(w τ)` — G3/G4 of the judge
pinned this numerically; if the Lean def differs syntactically, prove
`symWeighted_apply` refl/simp lemma first and use it everywhere.

## Part A — the unitary (elementary, no instance machinery)

The site form (`siteForm`) weighs by 1/w; embed real Euclidean vectors
by `Q u := fun σ => Real.sqrt (w σ) * u σ` (ℝ→ℂ coercion at the
statement boundary only).

- **A1 (isometry, pointwise):**
  `siteForm w (fun σ => (√(w σ) * u σ : ℂ)) (fun σ => (√(w σ) * v σ : ℂ))
     = (∑ σ, u σ * v σ : ℂ)`  for real `u v`.
  Proof: unfold `siteForm`; per-σ: `conj(√w·u)·(√w·v)/w = u·v` via
  `Complex.conj_ofReal`, `mul_div_assoc`, `Real.mul_self_sqrt (le_of_lt (hw σ))`.
  Pin traps: `Complex.ofReal_mul`, `Complex.ofReal_div` direction; do the
  algebra in ℝ first, coerce once (`push_cast` may fight `Real.sqrt` —
  prefer explicit `Complex.ofReal_*` rewrites).
- **A2 (conjugation):**  `transferOp w β (Q u) = Q (mulVec (symWeighted w β) u)`
  pointwise:  LHS σ = `w σ * Σ_τ K σ τ * √(w τ) * u τ`;
  RHS σ = `√(w σ) * Σ_τ √(w σ) K σ τ √(w τ) u τ`.  Equal by
  `√w·√w = w` pulled out of the sum (`Finset.mul_sum`, `mul_comm`
  shuffles).  State with `Matrix.mulVec` to match `opOf_apply`
  (`DobrushinTransport.opOf_apply` gives `opOf M v x = Σ τ, M x τ * v τ`
  — CHECK index order: mulVec is `Σ M x τ * v τ` ✓).
- **A3 (iterate):**  `(transferOp w β)^[n] (Q u) = Q (((symWeighted w β)^n).mulVec u)`
  by induction from A2 (`Function.iterate_succ_apply'`; matrix pow via
  `Matrix.pow_succ` — beware which side `pow_succ` multiplies; use
  `Matrix.mulVec_mulVec`).
- **A4 (norm transport for the endpoint, matrix-element form):**
  no operator-norm transport is needed — the endpoint's gap clause is
  stated on the Euclidean side exactly as `dobrushin_ising_uniform_gap`
  emits it (`‖projectedTransfer (opOf (tiltKernel (sliceW γ L) β lam))
  (vacOf Om)‖ ≤ exp (−m)`), and the OS-side clauses are connected to it
  by A1–A3 identities.  DO NOT attempt `LinearIsometryEquiv` packaging
  first (charter fallback is primary): matrix-element identities
  suffice for every stated clause.

## Part B — n-step identification (consume, then induct only if needed)

Target: the reconstructed two-point function against the MEASURE.

- **B1 (dressed n-step, real):**  from SpatialGibbs:
  `pathSum_eq_iterate` + `gibbsWeight_eq_dressed` give (shape, verify
  exact name/statement at fabrication): unnormalised strip two-point sum
  over `X : Fin (N+1) → Conf` of `gibbsWeight w β X * A (X 0) * B (X N)`
  equals the dressed matrix element `⟪√w·A, (symWeighted w β)^N (√w·B)⟫`.
  Judge G5 verified this numerically (raw = dressed, N = 1..4, five
  parameter cases).  If the in-tree lemma is stated for the OS lane's
  own kernel, bridge with the pointwise kernel-equality lemma of §0.
- **B2 (partition):** same with `A = B = 1` (judge: partition identity).
- **B3 (connected bound, the endpoint's clause (v)):** connected
  correlator = raw/Z − (rawA/Z)(rawB/Z); expand `S^N = lam^N (P_Ω + R)`
  with `R = projectedTransfer^N`; the SIX-term bound (judge G5's
  expansion — vacuum cross terms do NOT vanish):
  `|conn| ≤ [|a||b|·n1² + na·nb·c1² + 2·na·nb·n1²·rN + |a|·c1·n1·nb
             + na·n1·|b|·c1] · rN / zratio²`
  with `rN = e^{−mN}` from the D-6 feed and `zratio = Z/lam^N ≥ c1² −
  n1²·rN > 0` in-window for N ≥ N₀... CAREFUL: keep the statement
  DIVISION-SAFE: state the bound multiplied through by `Z²` (no
  quotient), i.e.  `|Z²·conn| ≤ (…)·rN·lam^{2N}` — quantifiers explicit,
  constants per (L, A, B) free, the RATE alone uniform.  This is the
  volume-uniform clustering clause; do not promise a normalised constant
  uniform in L (o-bridge: per-observable constants unconstrained).
- **B4 (complex corollary):** split A, B into re/im (`complexQuad_eq`
  pattern from SpatialOS); four applications of B3.

## Part C — the endpoint

```
theorem os_reconstruction_uniform_gap (β γ : ℝ) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α) (hβ : 0 ≤ β) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      -- (i) OS positivity of the reconstructed pairing (cite lane thm)
      (∀ (mdep : ℕ) (F : … → ℂ), 0 ≤ (osPairingBond (sliceW γ L) β mdep F F).re
          ∧ (osPairingBond … F F).im = 0) ∧   -- exact shape: reuse osPairingBond_nonneg
      -- (ii)+(iii) Perron data and the uniform gap on the Euclidean side
      (∃ (lam : ℝ) (Om : Conf L → ℝ), 0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        ‖projectedTransfer (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om)‖
          ≤ Real.exp (-m) ∧
        -- (iv) the transported reading: T∘Q = Q∘S and the site-form
        --      isometry, so the SAME lam,Om,m govern the OS operator
        (∀ u, transferOp (sliceW γ L) β (Qfun (sliceW γ L) u)
              = Qfun (sliceW γ L) ((symWeighted (sliceW γ L) β).mulVec u)) ∧
        -- (v) volume-uniform clustering of reconstructed correlators
        (∀ N A B, ‖Z²·conn …‖ ≤ C(L,A,B) * Real.exp (-m * N) * …))
```

(The exact clause list is a fabrication decision; the charter requires
every quantifier in the statement.  Clause (i) is a citation; (ii)–(iii)
come from `dobrushin_ising_uniform_gap` verbatim — same `m`, same
witnesses via `choose`; (iv) is A2; (v) is B3.  If the single big
statement fights elaboration, split into THREE named endpoint theorems
sharing the `∃ m` via a helper structure — house pattern: quantifiers in
Lean, never in prose.)

## Oracle endpoints (count them for the prediction)

`os_reconstruction_uniform_gap` (or its ≤3 split parts), A1, A2, B1, B3
— suggested +5 to +7 oracle reports.  Core: +1 module job (plus
whatever the pin charges for the import graph — the corollary's base is
8480 at `c7b870b05`; re-verify the baseline is unchanged at `c76b79050`
before predicting, since only docs/scripts were committed since).

## Known pin traps (from D-6's six passes — do not rediscover)

`Function.update_of_ne` / `update_self` names; `have` makes DATA opaque
(equivs/defs go in `let` or inline); Fintype instances stuck on meta
implicits → pin by name; `rw` blind to beta-redexes → `show` the
beta-reduced form; `Finset.sum_div` forward direction; congr cascades
vs divisions → single identification lemma; `positivity` blind to
opaque atoms → explicit `mul_nonneg` chains; rw's rfl auto-closes
`@[refl]` relations; `Real.mul_self_sqrt` needs `0 ≤`, use `le_of_lt ∘ hw`.
