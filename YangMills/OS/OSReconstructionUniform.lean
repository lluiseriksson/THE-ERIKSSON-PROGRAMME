/-
# OS-R module A — the transported volume-uniform gap

Campaign: docs/OS-RECONSTRUCTION-CHARTER.md (ledger Add. 608).
Licence: judge_os_uniform 110/110 on the Colab plane, normal AND -O,
three witnesses (this desk's terminal reads of the c2723e7ec run's
artefacts; the independent osr52 desk's tee'd transcripts at 174fd6dfd
persisted in osr0_licence_run.ipynb; the registered local run) —
ledger Addendum 613 at a545de4e5.
Blueprint: docs/OS-R-FABRICATION-BLUEPRINT.md; draft second pass:
docs/OS-R-MODULE-DRAFT.lean.txt.

Content (part A of the charter):
* `qEmbed` — the √w dressing of a real Euclidean vector, read as a
  complex boundary vector.  The unitary of the charter in its
  elementary, matrix-element form (the charter's PRIMARY route; no
  LinearIsometryEquiv packaging).
* A1 `siteForm_qEmbed` — the site form (which weighs by 1/w) of two
  dressed vectors is the plain Euclidean pairing.
* A2 `transferOp_qEmbed` — the forced transfer operator on a dressed
  vector is the dressing of the symmetrised kernel's action:
  `T (Q u) = Q (act (symWeighted w β) u)`.
* A3 `transferOp_iterate_qEmbed` — the n-fold iterate transports.
* `os_reconstruction_uniform_gap` — in the Dobrushin window with
  β ≥ 0: the Perron data and ONE m > 0 for EVERY spatial extent
  (`dobrushin_ising_uniform_gap`'s witnesses, verbatim), together with
  the transported reading (A2) that makes the bounded operator the
  transfer operator of the reconstructed (site-form) theory.

The n-step identification against the measure (part B) is the next
module pass; its bricks are drafted in the draft's B0a–B4.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry.
-/

import YangMills.OS.SpatialReconstruction
import YangMills.OS.DobrushinCorollary
import YangMills.OS.DobrushinTilt
import YangMills.OS.DobrushinTransport
import YangMills.OS.TransferGap

namespace YangMills.OS

open Finset

-- PASS 2 (plane): the endpoint's five names (sliceW, tiltKernel, opOf,
-- vacOf, dobrushin_ising_uniform_gap) live one namespace deeper -- the
-- whole D-lane nests `namespace Dobrushin` inside `YangMills.OS`
-- (DobrushinCorollary.lean:54 etc.).  Pass 1 never reached them: the
-- parser stopped at the binder error, so their "first-pass" status was
-- an overstatement, corrected in the ledger.  No collisions: the A-part
-- names (spatialKernel, symWeighted, act, dress, siteForm, transferOp)
-- have single declarations in YangMills.OS proper.
open Dobrushin

variable {L : ℕ}

/-! ## The dressing -/

/-- The embedding `Q`: a real Euclidean vector dressed by `√w`, read as a
complex boundary vector. -/
noncomputable def qEmbed (w : (Fin L → Fin 2) → ℝ) (u : (Fin L → Fin 2) → ℝ) :
    (Fin L → Fin 2) → ℂ :=
  fun σ => ((Real.sqrt (w σ) * u σ : ℝ) : ℂ)

/-- The dressing is `dress`, complexified — the seam into `SpatialGibbs`. -/
theorem qEmbed_eq_dress (w : (Fin L → Fin 2) → ℝ) (u : (Fin L → Fin 2) → ℝ) :
    qEmbed w u = fun σ => ((dress w u σ : ℝ) : ℂ) := rfl

/-! ## A1 — the isometry -/

/-- **The site form of two dressed vectors is the Euclidean pairing.**
Per site: `(√w·u) · (√w·v) · (1/w) = u·v`. -/
theorem siteForm_qEmbed (w : (Fin L → Fin 2) → ℝ) (hw : ∀ σ, 0 < w σ)
    (u v : (Fin L → Fin 2) → ℝ) :
    siteForm w (qEmbed w u) (qEmbed w v) = ((∑ σ, u σ * v σ : ℝ) : ℂ) := by
  unfold siteForm qEmbed
  have key : ∀ σ : Fin L → Fin 2,
      Real.sqrt (w σ) * u σ * (Real.sqrt (w σ) * v σ) * (1 / w σ)
        = u σ * v σ := by
    intro σ
    have hs : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
      Real.mul_self_sqrt (hw σ).le
    have hne : w σ ≠ 0 := (hw σ).ne'
    calc Real.sqrt (w σ) * u σ * (Real.sqrt (w σ) * v σ) * (1 / w σ)
        = (Real.sqrt (w σ) * Real.sqrt (w σ)) * (u σ * v σ) * (1 / w σ) := by
          ring
      _ = w σ * (u σ * v σ) * (1 / w σ) := by rw [hs]
      _ = (u σ * v σ) * (w σ * (1 / w σ)) := by ring
      _ = u σ * v σ := by rw [mul_one_div, div_self hne, mul_one]
  calc (∑ σ : Fin L → Fin 2,
        (starRingEnd ℂ) ((Real.sqrt (w σ) * u σ : ℝ) : ℂ)
          * ((Real.sqrt (w σ) * v σ : ℝ) : ℂ) * ((1 / w σ : ℝ) : ℂ))
      = ∑ σ : Fin L → Fin 2,
          ((Real.sqrt (w σ) * u σ * (Real.sqrt (w σ) * v σ) * (1 / w σ) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    _ = ((∑ σ, u σ * v σ : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun σ _ => congrArg _ (key σ)

/-! ## A2 — the conjugation -/

/-- **`T (Q u) = Q (S u)`**: the forced operator on a dressed vector is the
dressing of the symmetrised kernel's action.  Per site, `w σ` on the left
splits as `√(w σ)·√(w σ)`, one factor staying outside the sum. -/
theorem transferOp_qEmbed (w : (Fin L → Fin 2) → ℝ) (hw : ∀ σ, 0 < w σ)
    (β : ℝ) (u : (Fin L → Fin 2) → ℝ) :
    transferOp w β (qEmbed w u) = qEmbed w (act (symWeighted w β) u) := by
  funext σ
  unfold transferOp qEmbed act symWeighted
  have hs : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
    Real.mul_self_sqrt (hw σ).le
  have key : w σ * ∑ τ, spatialKernel β σ τ * (Real.sqrt (w τ) * u τ)
      = Real.sqrt (w σ)
          * ∑ τ, Real.sqrt (w σ) * spatialKernel β σ τ * Real.sqrt (w τ) * u τ := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    calc w σ * (spatialKernel β σ τ * (Real.sqrt (w τ) * u τ))
        = (Real.sqrt (w σ) * Real.sqrt (w σ))
            * (spatialKernel β σ τ * (Real.sqrt (w τ) * u τ)) := by rw [hs]
      _ = Real.sqrt (w σ)
            * (Real.sqrt (w σ) * spatialKernel β σ τ * Real.sqrt (w τ) * u τ) := by
          ring
  calc ((w σ : ℝ) : ℂ)
        * ∑ τ, ((spatialKernel β σ τ : ℝ) : ℂ) * ((Real.sqrt (w τ) * u τ : ℝ) : ℂ)
      = ((w σ * ∑ τ, spatialKernel β σ τ * (Real.sqrt (w τ) * u τ) : ℝ) : ℂ) := by
        -- PASS 1 (plane, ELAB_EXIT 1): the hand rewrite left the per-term cast
        -- `↑K * (↑√w * ↑u) = ↑(K * (√w * u))` unsolved.  push_cast owns the
        -- whole chain (Complex.ofReal_sum and ofReal_mul are norm_cast).
        push_cast
        ring
    _ = ((Real.sqrt (w σ)
          * ∑ τ, Real.sqrt (w σ) * spatialKernel β σ τ * Real.sqrt (w τ) * u τ : ℝ) : ℂ) := by
        rw [key]

/-! ## A3 — the iterate -/

/-- **`T^[n] (Q u) = Q (S^[n] u)`**, in `act` form — the shape
`gibbsPathSum_eq_iterate` consumes.  Induction on A2. -/
theorem transferOp_iterate_qEmbed (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (n : ℕ) (u : (Fin L → Fin 2) → ℝ) :
    (transferOp w β)^[n] (qEmbed w u)
      = qEmbed w ((act (symWeighted w β))^[n] u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact transferOp_qEmbed w hw β ((act (symWeighted w β))^[n] u)

/-! ## B0 — the operator-side bridges (pass 4)

`vacuumTransfer_opOf`, `opOf_symm`, `opOf_fix`, `vacOf_norm`,
`tiltKernel_symm` and `clustering_of_gap` are already in the tree; the
only new bricks are the tilt scaling and the act/opOf power bridge. -/

/-- **B0b — tilt scaling.**  The symmetrised action is `lam` times the
normalised (tilt) action, per site. -/
theorem act_symWeighted_eq_smul_act_tilt (w : (Fin L → Fin 2) → ℝ)
    (β lam : ℝ) (hlam : lam ≠ 0) (u : (Fin L → Fin 2) → ℝ) :
    act (symWeighted w β) u
      = fun σ => lam * act (fun a b => tiltKernel w β lam a b) u σ := by
  funext σ
  unfold act
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  -- PASS 4: rw is blind to the beta-redex `(fun a b => tiltKernel …) σ τ`
  -- (the D-6 pin trap, verbatim); `show` the reduced form first.
  show symWeighted w β σ τ * u τ = lam * (tiltKernel w β lam σ τ * u τ)
  rw [tiltKernel_apply]
  field_simp

/-- **B0a — the act/opOf power bridge.**  The `n`-fold `act` iterate is the
`n`-th operator power, pointwise, through `WithLp.toLp`. -/
theorem act_iterate_eq_opOf_pow
    (M : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℝ) (n : ℕ)
    (u : (Fin L → Fin 2) → ℝ) (σ : Fin L → Fin 2) :
    (act (fun a b => M a b))^[n] u σ
      = ((opOf M) ^ n) (WithLp.toLp 2 u) σ := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      have hstep : WithLp.toLp 2 (act (fun a b => M a b) u)
          = opOf M (WithLp.toLp 2 u) := by
        refine PiLp.ext fun y => ?_
        rw [opOf_apply]
        rfl
      rw [Function.iterate_succ_apply, pow_succ,
        ContinuousLinearMap.mul_apply, ← hstep]
      exact ih (act (fun a b => M a b) u)

/-! ## The endpoint — the transported volume-uniform gap -/

/-- **OS reconstruction with one mass.**  In the Dobrushin window with
`β ≥ 0`: there is ONE `m > 0` such that for EVERY spatial extent `L` the
D-6 Perron data exists (`lam`, `Om`, the fixed-point equation, and the
projected-operator bound `≤ exp (−m)`), and the forced transfer operator
of the reconstructed theory is unitarily the symmetrised kernel that data
governs (the A2 identity, stated at `w := sliceW γ L`).  The gap clause
is `dobrushin_ising_uniform_gap`'s, with the SAME witnesses. -/
-- PASS 1 (plane): 148:50 "expected token" landed on the implicit binder.
-- `α` is the section-variable letter Lean auto-binds in this file's scope, so
-- the explicit `{α : ℝ}` re-binder confused the parser; renamed to `alpha`
-- (the D-6 source is free to keep its own name — this is our binder).
theorem os_reconstruction_uniform_gap (β γ : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ alpha) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        ‖projectedTransfer (opOf (tiltKernel (sliceW γ L) β lam))
            (vacOf Om)‖ ≤ Real.exp (-m) ∧
        (∀ u, transferOp (sliceW γ L) β (qEmbed (sliceW γ L) u)
            = qEmbed (sliceW γ L) (act (symWeighted (sliceW γ L) β) u)) := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ halpha0 halpha1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  exact ⟨lam, Om, hlam, hOm, hfix, hnorm,
    fun u => transferOp_qEmbed (sliceW γ L) (sliceW_pos γ L) β u⟩

/-- **The volume-uniform clustering of the reconstructed operator.**  In
the Dobrushin window: ONE `m > 0` such that for EVERY spatial extent the
D-6 Perron data packages into a `VacuumTransfer`
(`vacuumTransfer_opOf`, with `tiltKernel_symm` and the fixed-point
clause), and `clustering_of_gap` reads the projected bound as geometric
decay of EVERY connected correlator of the transported transfer
operator: `|connCorr T Ω v n| ≤ ‖v‖² · (e^{-m})ⁿ`.  The constant is
per-observable (`‖v‖²`); the RATE alone is uniform in `L` — the
honesty split o-bridge demands. -/
theorem os_reconstruction_uniform_clustering (β γ : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ alpha) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        ∀ (v : EuclideanSpace ℝ (Fin (L + 1) → Fin 2)) (n : ℕ),
          |connCorr (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om) v n|
            ≤ ‖v‖ ^ 2 * Real.exp (-m) ^ n := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ halpha0 halpha1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  have hT : VacuumTransfer (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om) :=
    vacuumTransfer_opOf _ Om (tiltKernel_symm _ β lam) hOm hfix
  exact ⟨lam, Om, hlam, hOm, hfix,
    fun v n => clustering_of_gap hT hnorm v n⟩

end YangMills.OS
