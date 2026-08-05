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
open scoped RealInnerProductSpace

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

/-! ## B1/B2 — the raw Gibbs sums meet the operator powers (pass 8) -/

/-- `act` is homogeneous in the vector. -/
theorem act_smul_fun (K : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ) (c : ℝ)
    (u : (Fin L → Fin 2) → ℝ) :
    act K (fun τ => c * u τ) = fun σ => c * act K u σ := by
  funext σ
  unfold act
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

/-- Iterates of `act` pull scalars through. -/
theorem act_iterate_smul_fun (K : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ)
    (c : ℝ) (n : ℕ) (u : (Fin L → Fin 2) → ℝ) :
    (act K)^[n] (fun τ => c * u τ) = fun σ => c * (act K)^[n] u σ := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      funext σ
      rw [Function.iterate_succ_apply, act_smul_fun]
      have h := congrFun (ih (act K u)) σ
      rw [h, Function.iterate_succ_apply]

/-- Iterated tilt scaling: `(act S)^[n] = λⁿ · (act tilt)^[n]`. -/
theorem act_symWeighted_iterate_eq_smul_tilt (w : (Fin L → Fin 2) → ℝ)
    (β lam : ℝ) (hlam : lam ≠ 0) (n : ℕ) (u : (Fin L → Fin 2) → ℝ) :
    (act (symWeighted w β))^[n] u
      = fun σ => lam ^ n
          * (act (fun a b => tiltKernel w β lam a b))^[n] u σ := by
  induction n generalizing u with
  | zero => funext σ; simp
  | succ n ih =>
      funext σ
      rw [Function.iterate_succ_apply,
        act_symWeighted_eq_smul_act_tilt w β lam hlam u]
      have h1 := congrFun
        (ih (fun τ => lam * act (fun a b => tiltKernel w β lam a b) u τ)) σ
      rw [h1]
      have h2 := congrFun (act_iterate_smul_fun
        (fun a b => tiltKernel w β lam a b) lam n
        (act (fun a b => tiltKernel w β lam a b) u)) σ
      rw [h2, Function.iterate_succ_apply]
      ring

/-- **B1 — the raw Gibbs two-point sum IS `λᴺ` times a matrix element of the
operator powers.**  Exact identity, no bound. -/
theorem gibbsPathSum_eq_inner_pow (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) (β lam : ℝ) (hlam : lam ≠ 0) (N : ℕ)
    (A B : (Fin L → Fin 2) → ℝ) :
    gibbsPathSum w β N A B
      = lam ^ N * ⟪((opOf (tiltKernel w β lam)) ^ N)
          (WithLp.toLp 2 (dress w A)), WithLp.toLp 2 (dress w B)⟫ := by
  rw [gibbsPathSum_eq_iterate hw β N A B, inner_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := congrFun
    (act_symWeighted_iterate_eq_smul_tilt w β lam hlam N (dress w A)) σ
  rw [h1]
  have h2 := act_iterate_eq_opOf_pow (tiltKernel w β lam) N (dress w A) σ
  rw [h2]
  have h3 : (WithLp.toLp 2 (dress w B)) σ = dress w B σ := rfl
  rw [h3]
  ring

/-- **B2 — the partition function, same shape at the dressed constant.** -/
theorem gibbsPartition_eq_inner_pow (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) (β lam : ℝ) (hlam : lam ≠ 0) (N : ℕ) :
    gibbsPartition w β N
      = lam ^ N * ⟪((opOf (tiltKernel w β lam)) ^ N)
          (WithLp.toLp 2 (dress w (fun _ => 1))),
          WithLp.toLp 2 (dress w (fun _ => 1))⟫ := by
  have h : gibbsPartition w β N
      = gibbsPathSum w β N (fun _ => 1) (fun _ => 1) := by
    unfold gibbsPartition gibbsPathSum
    exact Finset.sum_congr rfl fun X _ => by ring
  rw [h, gibbsPathSum_eq_inner_pow w hw β lam hlam N]

/-! ## The mixed clustering machinery (generic Hilbert, pass 8) -/

section MixedHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Pythagoras: removing the vacuum component does not grow the norm. -/
theorem norm_sub_inner_smul_le (Om v : H) (hOm : ‖Om‖ = 1) :
    ‖v - (⟪Om, v⟫) • Om‖ ≤ ‖v‖ := by
  have hsq : ‖v - (⟪Om, v⟫) • Om‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hOm,
      real_inner_comm v Om]
    simp only [Real.norm_eq_abs, mul_one]
    nlinarith [sq_abs ((⟪v, Om⟫ : ℝ)), sq_abs ((⟪Om, v⟫ : ℝ)),
      sq_nonneg ((⟪v, Om⟫ : ℝ)), real_inner_comm v Om]
  nlinarith [norm_nonneg (v - (⟪Om, v⟫) • Om), norm_nonneg v]

/-- Powers of an operator obey the geometric norm bound. -/
theorem pow_apply_norm_le (S : H →L[ℝ] H) {r : ℝ} (hr : 0 ≤ r)
    (hS : ‖S‖ ≤ r) (v : H) (n : ℕ) : ‖(S ^ n) v‖ ≤ r ^ n * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (S ^ (n + 1)) v = S ((S ^ n) v) := by rw [pow_succ']; rfl
      calc ‖(S ^ (n + 1)) v‖ = ‖S ((S ^ n) v)‖ := by rw [hstep]
        _ ≤ ‖S‖ * ‖(S ^ n) v‖ := S.le_opNorm _
        _ ≤ r * (r ^ n * ‖v‖) :=
            mul_le_mul hS ih (norm_nonneg _) hr
        _ = r ^ (n + 1) * ‖v‖ := by ring

/-- **Mixed clustering from the gap** — two independent observables, the
zero-time case included. -/
theorem mixed_connCorr_bound {T : H →L[ℝ] H} {Om : H}
    (hT : VacuumTransfer T Om) {r : ℝ} (hr : 0 ≤ r)
    (hgap : ‖projectedTransfer T Om‖ ≤ r) (u v : H) (n : ℕ) :
    |(⟪u, (T ^ n) v⟫) - (⟪Om, u⟫) * (⟪Om, v⟫)|
      ≤ ‖u‖ * ‖v‖ * r ^ n := by
  have hkey : (⟪u, (T ^ n) v⟫) - (⟪Om, u⟫) * (⟪Om, v⟫)
      = ⟪u, (T ^ n) v - (⟪Om, v⟫) • Om⟫ := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_comm u Om]
    ring
  rw [hkey]
  cases n with
  | zero =>
      have h0 : ((T ^ 0) v) = v := by simp
      rw [h0, pow_zero, mul_one]
      calc |⟪u, v - (⟪Om, v⟫) • Om⟫|
            ≤ ‖u‖ * ‖v - (⟪Om, v⟫) • Om‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖u‖ * ‖v‖ := mul_le_mul_of_nonneg_left
            (norm_sub_inner_smul_le Om v hT.unit) (norm_nonneg u)
  | succ m =>
      rw [← hT.projected_pow_succ v m]
      calc |⟪u, (projectedTransfer T Om ^ (m + 1)) v⟫|
            ≤ ‖u‖ * ‖(projectedTransfer T Om ^ (m + 1)) v‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖u‖ * (r ^ (m + 1) * ‖v‖) := mul_le_mul_of_nonneg_left
            (pow_apply_norm_le _ hr hgap v (m + 1)) (norm_nonneg u)
        _ = ‖u‖ * ‖v‖ * r ^ (m + 1) := by ring

/-- The triangle inequality for a difference, in the shape the ratio estimate
consumes. -/
theorem abs_sub_le_add_abs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
    _ ≤ |x| + |-y| := abs_add_le x (-y)
    _ = |x| + |y| := by rw [abs_neg]

/-- **The vacuum ratio, with an exponential rate.**  Two matrix elements of the
SAME power, divided: the quotient sits within `r^N` of the vacuum ratio
`⟪Ω,qA⟫/⟪Ω,q1⟫` — an expression that does NOT mention the far-end vector `qB`.
That is the whole content: the limit exists, it is the vacuum state, and the
boundary vector has been forgotten.  The denominator floor `d` is a hypothesis
here; the positive cone supplies it downstream. -/
theorem inner_ratio_approx {T : H →L[ℝ] H} {Om : H}
    (hT : VacuumTransfer T Om) {r : ℝ} (hr : 0 ≤ r)
    (hgap : ‖projectedTransfer T Om‖ ≤ r) (qA q1 qB : H) (N : ℕ)
    {d : ℝ} (hd : 0 < d) (hden : d ≤ ⟪q1, (T ^ N) qB⟫)
    (hOm1 : 0 < (⟪Om, q1⟫ : ℝ)) :
    |⟪qA, (T ^ N) qB⟫ / ⟪q1, (T ^ N) qB⟫ - ⟪Om, qA⟫ / ⟪Om, q1⟫|
      ≤ 2 * ‖qA‖ * ‖qB‖ * ‖q1‖ / (d * ⟪Om, q1⟫) * r ^ N := by
  have hEA := mixed_connCorr_bound hT hr hgap qA qB N
  have hE1 := mixed_connCorr_bound hT hr hgap q1 qB N
  have hbpos : (0 : ℝ) < ⟪q1, (T ^ N) qB⟫ := lt_of_lt_of_le hd hden
  have hbne : (⟪q1, (T ^ N) qB⟫ : ℝ) ≠ 0 := hbpos.ne'
  have hOm1ne : (⟪Om, q1⟫ : ℝ) ≠ 0 := hOm1.ne'
  have hdb : d * (⟪Om, q1⟫ : ℝ) ≠ 0 := (mul_pos hd hOm1).ne'
  have hA : |(⟪Om, qA⟫ : ℝ)| ≤ ‖qA‖ := by
    have h := abs_real_inner_le_norm Om qA
    rwa [hT.unit, one_mul] at h
  have h1 : |(⟪Om, q1⟫ : ℝ)| ≤ ‖q1‖ := by
    have h := abs_real_inner_le_norm Om q1
    rwa [hT.unit, one_mul] at h
  have hid : ⟪qA, (T ^ N) qB⟫ / ⟪q1, (T ^ N) qB⟫ - ⟪Om, qA⟫ / ⟪Om, q1⟫
      = ((⟪qA, (T ^ N) qB⟫ - ⟪Om, qA⟫ * ⟪Om, qB⟫) * ⟪Om, q1⟫
          - ⟪Om, qA⟫ * (⟪q1, (T ^ N) qB⟫ - ⟪Om, q1⟫ * ⟪Om, qB⟫))
        / (⟪q1, (T ^ N) qB⟫ * ⟪Om, q1⟫) := by
    field_simp <;> ring
  have hnum : |(⟪qA, (T ^ N) qB⟫ - ⟪Om, qA⟫ * ⟪Om, qB⟫) * ⟪Om, q1⟫
        - ⟪Om, qA⟫ * (⟪q1, (T ^ N) qB⟫ - ⟪Om, q1⟫ * ⟪Om, qB⟫)|
      ≤ 2 * ‖qA‖ * ‖qB‖ * ‖q1‖ * r ^ N := by
    have t1 : |(⟪qA, (T ^ N) qB⟫ - ⟪Om, qA⟫ * ⟪Om, qB⟫) * ⟪Om, q1⟫|
        ≤ ‖qA‖ * ‖qB‖ * r ^ N * ‖q1‖ := by
      rw [abs_mul]
      exact mul_le_mul hEA h1 (abs_nonneg _)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg hr N))
    have t2 : |⟪Om, qA⟫ * (⟪q1, (T ^ N) qB⟫ - ⟪Om, q1⟫ * ⟪Om, qB⟫)|
        ≤ ‖qA‖ * (‖q1‖ * ‖qB‖ * r ^ N) := by
      rw [abs_mul]
      exact mul_le_mul hA hE1 (abs_nonneg _) (norm_nonneg _)
    calc |(⟪qA, (T ^ N) qB⟫ - ⟪Om, qA⟫ * ⟪Om, qB⟫) * ⟪Om, q1⟫
          - ⟪Om, qA⟫ * (⟪q1, (T ^ N) qB⟫ - ⟪Om, q1⟫ * ⟪Om, qB⟫)|
        ≤ |(⟪qA, (T ^ N) qB⟫ - ⟪Om, qA⟫ * ⟪Om, qB⟫) * ⟪Om, q1⟫|
            + |⟪Om, qA⟫ * (⟪q1, (T ^ N) qB⟫ - ⟪Om, q1⟫ * ⟪Om, qB⟫)| :=
          abs_sub_le_add_abs _ _
      _ ≤ ‖qA‖ * ‖qB‖ * r ^ N * ‖q1‖ + ‖qA‖ * (‖q1‖ * ‖qB‖ * r ^ N) :=
          add_le_add t1 t2
      _ = 2 * ‖qA‖ * ‖qB‖ * ‖q1‖ * r ^ N := by ring
  have hcoef : (0 : ℝ) ≤ 2 * ‖qA‖ * ‖qB‖ * ‖q1‖ / (d * ⟪Om, q1⟫) * r ^ N :=
    mul_nonneg (div_nonneg (by positivity) (le_of_lt (mul_pos hd hOm1)))
      (pow_nonneg hr N)
  rw [hid, abs_div, abs_of_pos (mul_pos hbpos hOm1),
    div_le_iff₀ (mul_pos hbpos hOm1)]
  calc |(⟪qA, (T ^ N) qB⟫ - ⟪Om, qA⟫ * ⟪Om, qB⟫) * ⟪Om, q1⟫
        - ⟪Om, qA⟫ * (⟪q1, (T ^ N) qB⟫ - ⟪Om, q1⟫ * ⟪Om, qB⟫)|
      ≤ 2 * ‖qA‖ * ‖qB‖ * ‖q1‖ * r ^ N := hnum
    _ = 2 * ‖qA‖ * ‖qB‖ * ‖q1‖ / (d * ⟪Om, q1⟫) * r ^ N * (d * ⟪Om, q1⟫) := by
        field_simp <;> ring
    _ ≤ 2 * ‖qA‖ * ‖qB‖ * ‖q1‖ / (d * ⟪Om, q1⟫) * r ^ N
          * (⟪q1, (T ^ N) qB⟫ * ⟪Om, q1⟫) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hden hOm1.le) hcoef

/-! ## The division-safe six-term connected bound (pass 12) -/

/-- **The six-term connected bound, division-free.**  With
`F u v := ⟪u, Tᴺ v⟫`: the truncated combination
`F 1 1 · F A B − F A 1 · F 1 B` decays at the gap rate with the crude
honest constant `6‖A‖‖B‖‖1‖²`.  The proof is the ring identity in
E-terms (`E u v := F u v − ⟪Ω,u⟫⟪Ω,v⟫`): the pure product terms cancel
exactly, and each of the six surviving terms carries at least one `E`,
bounded by `mixed_connCorr_bound`; the two `E·E` terms spend one factor
`rᴺ ≤ 1`. -/
theorem six_term_connected_bound {T : H →L[ℝ] H} {Om : H}
    (hT : VacuumTransfer T Om) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hgap : ‖projectedTransfer T Om‖ ≤ r) (qA qB q1 : H) (N : ℕ) :
    |⟪q1, (T ^ N) q1⟫ * ⟪qA, (T ^ N) qB⟫
        - ⟪qA, (T ^ N) q1⟫ * ⟪q1, (T ^ N) qB⟫|
      ≤ 6 * ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by
  have hEAB := mixed_connCorr_bound hT hr hgap qA qB N
  have hE11 := mixed_connCorr_bound hT hr hgap q1 q1 N
  have hEA1 := mixed_connCorr_bound hT hr hgap qA q1 N
  have hE1B := mixed_connCorr_bound hT hr hgap q1 qB N
  have hA : |(⟪Om, qA⟫ : ℝ)| ≤ ‖qA‖ := by
    have h := abs_real_inner_le_norm Om qA
    rwa [hT.unit, one_mul] at h
  have hB : |(⟪Om, qB⟫ : ℝ)| ≤ ‖qB‖ := by
    have h := abs_real_inner_le_norm Om qB
    rwa [hT.unit, one_mul] at h
  have hC : |(⟪Om, q1⟫ : ℝ)| ≤ ‖q1‖ := by
    have h := abs_real_inner_le_norm Om q1
    rwa [hT.unit, one_mul] at h
  have hrN : (0 : ℝ) ≤ r ^ N := pow_nonneg hr N
  have hrN1 : r ^ N ≤ 1 := pow_le_one₀ hr hr1
  set FAB : ℝ := ⟪qA, (T ^ N) qB⟫ with hFAB_def
  set F11 : ℝ := ⟪q1, (T ^ N) q1⟫ with hF11_def
  set FA1 : ℝ := ⟪qA, (T ^ N) q1⟫ with hFA1_def
  set F1B : ℝ := ⟪q1, (T ^ N) qB⟫ with hF1B_def
  set a : ℝ := ⟪Om, qA⟫ with ha_def
  set b : ℝ := ⟪Om, qB⟫ with hb_def
  set c : ℝ := ⟪Om, q1⟫ with hc_def
  have h1 : |c * c * (FAB - a * b)| ≤ ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by
    rw [abs_mul, abs_mul]
    calc |c| * |c| * |FAB - a * b|
        ≤ ‖q1‖ * ‖q1‖ * (‖qA‖ * ‖qB‖ * r ^ N) :=
          mul_le_mul (mul_le_mul hC hC (abs_nonneg _) (norm_nonneg _))
            hEAB (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by ring
  have h2 : |a * b * (F11 - c * c)| ≤ ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by
    rw [abs_mul, abs_mul]
    calc |a| * |b| * |F11 - c * c|
        ≤ ‖qA‖ * ‖qB‖ * (‖q1‖ * ‖q1‖ * r ^ N) :=
          mul_le_mul (mul_le_mul hA hB (abs_nonneg _) (norm_nonneg _))
            hE11 (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by ring
  have h3 : |(F11 - c * c) * (FAB - a * b)|
      ≤ ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by
    rw [abs_mul]
    calc |F11 - c * c| * |FAB - a * b|
        ≤ (‖q1‖ * ‖q1‖ * r ^ N) * (‖qA‖ * ‖qB‖ * r ^ N) :=
          mul_le_mul hE11 hEAB (abs_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hrN)
      _ = (‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N) * r ^ N := by ring
      _ ≤ (‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N) * 1 :=
          mul_le_mul_of_nonneg_left hrN1 (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 2)) hrN)
      _ = ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := mul_one _
  have h4 : |a * c * (F1B - c * b)| ≤ ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by
    rw [abs_mul, abs_mul]
    calc |a| * |c| * |F1B - c * b|
        ≤ ‖qA‖ * ‖q1‖ * (‖q1‖ * ‖qB‖ * r ^ N) :=
          mul_le_mul (mul_le_mul hA hC (abs_nonneg _) (norm_nonneg _))
            hE1B (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by ring
  have h5 : |c * b * (FA1 - a * c)| ≤ ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by
    rw [abs_mul, abs_mul]
    calc |c| * |b| * |FA1 - a * c|
        ≤ ‖q1‖ * ‖qB‖ * (‖qA‖ * ‖q1‖ * r ^ N) :=
          mul_le_mul (mul_le_mul hC hB (abs_nonneg _) (norm_nonneg _))
            hEA1 (abs_nonneg _) (by positivity)
      _ = ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by ring
  have h6 : |(FA1 - a * c) * (F1B - c * b)|
      ≤ ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := by
    rw [abs_mul]
    calc |FA1 - a * c| * |F1B - c * b|
        ≤ (‖qA‖ * ‖q1‖ * r ^ N) * (‖q1‖ * ‖qB‖ * r ^ N) :=
          mul_le_mul hEA1 hE1B (abs_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hrN)
      _ = (‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N) * r ^ N := by ring
      _ ≤ (‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N) * 1 :=
          mul_le_mul_of_nonneg_left hrN1 (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 2)) hrN)
      _ = ‖qA‖ * ‖qB‖ * ‖q1‖ ^ 2 * r ^ N := mul_one _
  have key : F11 * FAB - FA1 * F1B
      = c * c * (FAB - a * b) + a * b * (F11 - c * c)
          + (F11 - c * c) * (FAB - a * b)
          - a * c * (F1B - c * b) - c * b * (FA1 - a * c)
          - (FA1 - a * c) * (F1B - c * b) := by ring
  have tri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
      _ ≤ |x| + |-y| := abs_add_le x (-y)
      _ = |x| + |y| := by rw [abs_neg]
  rw [key]
  have s1 := tri (c * c * (FAB - a * b) + a * b * (F11 - c * c)
      + (F11 - c * c) * (FAB - a * b)
      - a * c * (F1B - c * b) - c * b * (FA1 - a * c))
    ((FA1 - a * c) * (F1B - c * b))
  have s2 := tri (c * c * (FAB - a * b) + a * b * (F11 - c * c)
      + (F11 - c * c) * (FAB - a * b)
      - a * c * (F1B - c * b))
    (c * b * (FA1 - a * c))
  have s3 := tri (c * c * (FAB - a * b) + a * b * (F11 - c * c)
      + (F11 - c * c) * (FAB - a * b))
    (a * c * (F1B - c * b))
  have s4 := abs_add_le (c * c * (FAB - a * b) + a * b * (F11 - c * c))
    ((F11 - c * c) * (FAB - a * b))
  have s5 := abs_add_le (c * c * (FAB - a * b)) (a * b * (F11 - c * c))
  linarith [h1, h2, h3, h4, h5, h6]

end MixedHilbert

/-- **The reconstructed theory has one mass, measured against the raw Gibbs
sums.**  In the window: ONE `m > 0` such that for EVERY spatial extent the
D-6 data exist, the raw Gibbs two-point sum equals `λᴺ` times a matrix
element of the operator powers (EXACT identity, dressed observables), and
every MIXED connected correlator of the transported operator decays at the
rate `m` with per-observable constants — the zero-time case included. -/
theorem os_reconstruction_measure_uniform (β γ : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ alpha) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        (∀ (N : ℕ) (A B : (Fin (L + 1) → Fin 2) → ℝ),
          gibbsPathSum (sliceW γ L) β N A B
            = lam ^ N * ⟪((opOf (tiltKernel (sliceW γ L) β lam)) ^ N)
                (WithLp.toLp 2 (dress (sliceW γ L) A)),
                WithLp.toLp 2 (dress (sliceW γ L) B)⟫) ∧
        (∀ (u v : EuclideanSpace ℝ (Fin (L + 1) → Fin 2)) (n : ℕ),
          |(⟪u, ((opOf (tiltKernel (sliceW γ L) β lam)) ^ n) v⟫)
              - (⟪vacOf Om, u⟫) * (⟪vacOf Om, v⟫)|
            ≤ ‖u‖ * ‖v‖ * Real.exp (-m) ^ n) := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ halpha0 halpha1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  have hT : VacuumTransfer (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om) :=
    vacuumTransfer_opOf _ Om (tiltKernel_symm _ β lam) hOm hfix
  exact ⟨lam, Om, hlam, hOm, hfix,
    fun N A B => gibbsPathSum_eq_inner_pow (sliceW γ L) (sliceW_pos γ L)
      β lam hlam.ne' N A B,
    fun u v n => mixed_connCorr_bound hT (Real.exp_nonneg _) hnorm u v n⟩

/-! ## The positive cone — a denominator floor uniform in `N` (pass 17)

The parity obstruction of the previous version is not intrinsic: it was an
artefact of trying to bound `⟪T̂ᴺ q, q⟫` from below by SPECTRAL means (only the
even powers are positive semidefinite).  The kernel here is entrywise
POSITIVE, so the order-theoretic route works at every `N`: the ray through the
positive fixed vector is preserved, and it never collapses. -/

/-- The tilt kernel is entrywise POSITIVE for a positive weight and a positive
scale — at EVERY real `β`, since `spatialKernel` is a product of positive bond
factors (`spatialKernel_pos`). -/
theorem tiltKernel_pos (w : (Fin L → Fin 2) → ℝ) (hw : ∀ σ, 0 < w σ)
    (β lam : ℝ) (hlam : 0 < lam) (σ τ : Fin L → Fin 2) :
    0 < tiltKernel w β lam σ τ := by
  rw [tiltKernel_apply]
  have hsym : 0 < symWeighted w β σ τ := by
    unfold symWeighted
    exact mul_pos (mul_pos (Real.sqrt_pos.mpr (hw σ)) (spatialKernel_pos β σ τ))
      (Real.sqrt_pos.mpr (hw τ))
  exact div_pos hsym hlam

/-- The normalised vacuum of a positive Perron vector is positive entrywise. -/
theorem vacOf_pos (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (σ : Fin L → Fin 2) : 0 < vacOf Om σ := by
  have hS : (0 : ℝ) < ∑ y, Om y * Om y :=
    Finset.sum_pos (fun y _ => mul_pos (hOm y) (hOm y))
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  have hx : vacOf Om σ = Om σ / Real.sqrt (∑ y, Om y * Om y) := rfl
  rw [hx]
  exact div_pos (hOm σ) (Real.sqrt_pos.mpr hS)

/-- **The cone constant.**  A positive vector dominates a positive multiple of
the positive vacuum; the multiple is the in-tree finite minimum of the ratio. -/
theorem exists_cone_constant (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (v : EuclideanSpace ℝ (Fin L → Fin 2)) (hv : ∀ σ, 0 < v σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ, c * vacOf Om σ ≤ v σ := by
  have hvac : ∀ σ, 0 < vacOf Om σ := vacOf_pos Om hOm
  refine ⟨minWeight (fun σ => v σ / vacOf Om σ),
    minWeight_pos (fun σ => div_pos (hv σ) (hvac σ)), fun σ => ?_⟩
  have h1 : minWeight (fun σ => v σ / vacOf Om σ) ≤ v σ / vacOf Om σ :=
    minWeight_le _ σ
  have h2 := mul_le_mul_of_nonneg_right h1 (hvac σ).le
  have hne : vacOf Om σ ≠ 0 := (hvac σ).ne'
  have h3 : v σ / vacOf Om σ * vacOf Om σ = v σ := by
    field_simp
  rwa [h3] at h2

/-- **Cone propagation.**  A nonnegative kernel with a fixed vector `Ω` pushes
the ray `c·Ω` up through EVERY power: `c·Ω ≤ v` entrywise gives
`c·Ω ≤ T^n v` entrywise, for all `n`.  No parity, no spectral input. -/
theorem opOf_pow_ge_smul_fix (M : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℝ)
    (hM : ∀ σ τ, 0 ≤ M σ τ) (Om : EuclideanSpace ℝ (Fin L → Fin 2))
    (hfix : opOf M Om = Om) (c : ℝ) (v : EuclideanSpace ℝ (Fin L → Fin 2))
    (hv : ∀ σ, c * Om σ ≤ v σ) (n : ℕ) :
    ∀ σ, c * Om σ ≤ ((opOf M) ^ n) v σ := by
  induction n with
  | zero => intro σ; simpa using hv σ
  | succ n ih =>
      intro σ
      have hstep : ((opOf M) ^ (n + 1)) v = opOf M (((opOf M) ^ n) v) := by
        rw [pow_succ']; rfl
      have hfixσ : ∑ τ, M σ τ * Om τ = Om σ := by
        rw [← opOf_apply M Om σ, hfix]
      rw [hstep, opOf_apply]
      calc c * Om σ = c * ∑ τ, M σ τ * Om τ := by rw [hfixσ]
        _ = ∑ τ, M σ τ * (c * Om τ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun τ _ => by ring
        _ ≤ ∑ τ, M σ τ * (((opOf M) ^ n) v τ) :=
            Finset.sum_le_sum fun τ _ =>
              mul_le_mul_of_nonneg_left (ih τ) (hM σ τ)

/-- **THE DENOMINATOR FLOOR, UNIFORM IN `N`.**  For a nonnegative kernel whose
normalised positive vector is fixed, the diagonal matrix elements of the powers
against a POSITIVE vector never fall below a positive constant depending only
on the data — not on `N`.  The constant is `c²‖Ω‖²` with `c` the minimum of the
ratio `v/Ω` (in-tree `minWeight`, a genuine finite minimum). -/
theorem inner_pow_floor (M : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℝ)
    (hM : ∀ σ τ, 0 ≤ M σ τ) (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (hfix : opOf M (vacOf Om) = vacOf Om)
    (v : EuclideanSpace ℝ (Fin L → Fin 2)) (hv : ∀ σ, 0 < v σ) :
    ∃ f : ℝ, 0 < f ∧ ∀ n : ℕ, f ≤ ⟪((opOf M) ^ n) v, v⟫ := by
  have hvac : ∀ σ, 0 < vacOf Om σ := vacOf_pos Om hOm
  obtain ⟨c, hcpos, hcone⟩ := exists_cone_constant Om hOm v hv
  refine ⟨c ^ 2 * ∑ σ, vacOf Om σ * vacOf Om σ, ?_, fun n => ?_⟩
  · exact mul_pos (pow_pos hcpos 2)
      (Finset.sum_pos (fun σ _ => mul_pos (hvac σ) (hvac σ))
        ⟨Classical.arbitrary _, Finset.mem_univ _⟩)
  · have hprop := opOf_pow_ge_smul_fix M hM (vacOf Om) hfix c v hcone n
    rw [inner_eq_sum]
    calc c ^ 2 * ∑ σ, vacOf Om σ * vacOf Om σ
        = ∑ σ, (c * vacOf Om σ) * (c * vacOf Om σ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
      _ ≤ ∑ σ, (((opOf M) ^ n) v σ) * (c * vacOf Om σ) :=
          Finset.sum_le_sum fun σ _ =>
            mul_le_mul_of_nonneg_right (hprop σ)
              (mul_nonneg hcpos.le (hvac σ).le)
      _ ≤ ∑ σ, (((opOf M) ^ n) v σ) * v σ :=
          Finset.sum_le_sum fun σ _ =>
            mul_le_mul_of_nonneg_left (hcone σ)
              (le_trans (mul_nonneg hcpos.le (hvac σ).le) (hprop σ))

/-- **THE OFF-DIAGONAL FLOOR, UNIFORM IN `N`.**  Same cone, one index freed:
for two positive vectors the matrix elements `⟪Tⁿ u, v⟫` stay above a positive
constant that does not depend on `n`.  This is what licenses dividing by a
two-point sum whose far end carries an arbitrary positive boundary
observable. -/
theorem inner_pow_floor_offdiag
    (M : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℝ) (hM : ∀ σ τ, 0 ≤ M σ τ)
    (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (hfix : opOf M (vacOf Om) = vacOf Om)
    (u v : EuclideanSpace ℝ (Fin L → Fin 2))
    (hu : ∀ σ, 0 < u σ) (hv : ∀ σ, 0 < v σ) :
    ∃ f : ℝ, 0 < f ∧ ∀ n : ℕ, f ≤ ⟪((opOf M) ^ n) u, v⟫ := by
  have hvac : ∀ σ, 0 < vacOf Om σ := vacOf_pos Om hOm
  obtain ⟨c, hcpos, hcone⟩ := exists_cone_constant Om hOm u hu
  have hpair : (0 : ℝ) < ∑ σ, vacOf Om σ * v σ :=
    Finset.sum_pos (fun σ _ => mul_pos (hvac σ) (hv σ))
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  refine ⟨c * ∑ σ, vacOf Om σ * v σ, mul_pos hcpos hpair, fun n => ?_⟩
  have hprop := opOf_pow_ge_smul_fix M hM (vacOf Om) hfix c u hcone n
  rw [inner_eq_sum]
  calc c * ∑ σ, vacOf Om σ * v σ
      = ∑ σ, (c * vacOf Om σ) * v σ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ ≤ ∑ σ, (((opOf M) ^ n) u σ) * v σ :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_right (hprop σ) (hv σ).le

/-! ## The Gibbs-side six-term bound with explicit hypotheses -/

/-- The scale factor of the two-point/partition identities, pulled out of an
absolute value.  Pure algebra, isolated so the endpoints stay readable. -/
theorem abs_scaled_cross_le {lam : ℝ} (hlam : 0 < lam) (N : ℕ)
    (p q s t K rN : ℝ) (h : |p * q - s * t| ≤ K * rN) :
    |lam ^ N * p * (lam ^ N * q) - lam ^ N * s * (lam ^ N * t)|
      ≤ lam ^ (2 * N) * K * rN := by
  have hrw : lam ^ N * p * (lam ^ N * q) - lam ^ N * s * (lam ^ N * t)
      = lam ^ (2 * N) * (p * q - s * t) := by
    rw [pow_mul]
    ring
  rw [hrw, abs_mul, abs_of_nonneg (le_of_lt (pow_pos hlam (2 * N)))]
  calc lam ^ (2 * N) * |p * q - s * t|
      ≤ lam ^ (2 * N) * (K * rN) :=
        mul_le_mul_of_nonneg_left h (le_of_lt (pow_pos hlam (2 * N)))
    _ = lam ^ (2 * N) * K * rN := by ring

/-- **The six-term connected bound in raw Gibbs terms, hypotheses explicit.**
Both endpoints below consume this one algebra. -/
theorem gibbs_six_term_bound (w : (Fin L → Fin 2) → ℝ) (hw : ∀ σ, 0 < w σ)
    (β lam : ℝ) (hlam : 0 < lam) (Om : (Fin L → Fin 2) → ℝ)
    (hT : VacuumTransfer (opOf (tiltKernel w β lam)) (vacOf Om))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hgap : ‖projectedTransfer (opOf (tiltKernel w β lam)) (vacOf Om)‖ ≤ r)
    (N : ℕ) (A B : (Fin L → Fin 2) → ℝ) :
    |gibbsPartition w β N * gibbsPathSum w β N A B
        - gibbsPathSum w β N A (fun _ => 1)
          * gibbsPathSum w β N (fun _ => 1) B|
      ≤ lam ^ (2 * N)
          * (6 * ‖WithLp.toLp 2 (dress w A)‖ * ‖WithLp.toLp 2 (dress w B)‖
              * ‖WithLp.toLp 2 (dress w (fun _ => 1))‖ ^ 2)
          * r ^ N := by
  have hsix := six_term_connected_bound hT hr0 hr1 hgap
    (WithLp.toLp 2 (dress w A)) (WithLp.toLp 2 (dress w B))
    (WithLp.toLp 2 (dress w (fun _ => 1))) N
  have hAB := gibbsPathSum_eq_inner_pow w hw β lam hlam.ne' N A B
  have hA1 := gibbsPathSum_eq_inner_pow w hw β lam hlam.ne' N A (fun _ => 1)
  have h1B := gibbsPathSum_eq_inner_pow w hw β lam hlam.ne' N (fun _ => 1) B
  have hZ := gibbsPartition_eq_inner_pow w hw β lam hlam.ne' N
  have hsymm := hT.pow_symm N
  rw [hAB, hA1, h1B, hZ, hsymm, hsymm, hsymm, hsymm]
  exact abs_scaled_cross_le hlam N _ _ _ _ _ _ hsix

/-- **The division-safe connected bound in raw Gibbs terms.**  In the
window: ONE `m > 0` such that for EVERY spatial extent, every time depth
`N` and all real observables `A, B`, the truncated combination
`Z_N · S_N(A,B) − S_N(A,1) · S_N(1,B)` is bounded by `lam^(2N)` times the
crude honest constant `6‖QA‖‖QB‖‖Q1‖²` times `(e^{-m})^N`.  This is the
normalised connected-correlator bound multiplied through by the positive
scale of `Z_N²`: no division is performed, no denominator floor is
needed, and dividing by `Z_N² = lam^(2N)·⟪Q1, T̂^N Q1⟫²` recovers the
normalised statement in prose.  Witnesses are D-6's, consumed through
B1/B2 and `pow_symm`. -/
theorem os_reconstruction_connected_uniform (β γ : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ alpha) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        ∀ (N : ℕ) (A B : (Fin (L + 1) → Fin 2) → ℝ),
          |gibbsPartition (sliceW γ L) β N
                * gibbsPathSum (sliceW γ L) β N A B
              - gibbsPathSum (sliceW γ L) β N A (fun _ => 1)
                * gibbsPathSum (sliceW γ L) β N (fun _ => 1) B|
            ≤ lam ^ (2 * N)
                * (6 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
                    * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
                    * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖ ^ 2)
                * Real.exp (-m) ^ N := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ halpha0 halpha1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  have hT : VacuumTransfer (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om) :=
    vacuumTransfer_opOf _ Om (tiltKernel_symm _ β lam) hOm hfix
  have hexp1 : Real.exp (-m) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  exact ⟨lam, Om, hlam, hOm, hfix, fun N A B =>
    gibbs_six_term_bound (sliceW γ L) (sliceW_pos γ L) β lam hlam Om hT
      (Real.exp_nonneg _) hexp1 hnorm N A B⟩

/-- **THE NORMALISED CONNECTED CORRELATOR OF THE GIBBS MEASURE DECAYS AT THE
UNIFORM RATE.**  In the window: ONE `m > 0` such that for EVERY spatial extent
the partition function is positive at every depth AND there is a constant
`C A B` — depending on the observables and the extent, but NOT on the time
depth `N` — with
`|⟨A(X₀)B(X_N)⟩ − ⟨A(X₀)⟩⟨B(X_N)⟩| ≤ C A B · e^{-mN}`,
the expectations taken in the NORMALISED Gibbs measure.  This is the
division-free bound divided through by `Z_N²`; what makes the division safe is
the positive cone (`inner_pow_floor`): `tiltKernel` is entrywise positive and
the vacuum is positive and fixed, so `⟪T̂ᴺ Q1, Q1⟫` never falls below a positive
constant, at EVERY `N` — even and odd alike. -/
theorem os_reconstruction_normalised_clustering (β γ : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ alpha) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      (∀ N : ℕ, 0 < gibbsPartition (sliceW γ L) β N) ∧
      ∃ C : ((Fin (L + 1) → Fin 2) → ℝ) → ((Fin (L + 1) → Fin 2) → ℝ) → ℝ,
        (∀ A B, 0 ≤ C A B) ∧
        ∀ (N : ℕ) (A B : (Fin (L + 1) → Fin 2) → ℝ),
          |gibbsPathSum (sliceW γ L) β N A B / gibbsPartition (sliceW γ L) β N
              - gibbsPathSum (sliceW γ L) β N A (fun _ => 1)
                  / gibbsPartition (sliceW γ L) β N
                * (gibbsPathSum (sliceW γ L) β N (fun _ => 1) B
                    / gibbsPartition (sliceW γ L) β N)|
            ≤ C A B * Real.exp (-m) ^ N := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ halpha0 halpha1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  have hw := sliceW_pos γ L
  have hT : VacuumTransfer (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om) :=
    vacuumTransfer_opOf _ Om (tiltKernel_symm _ β lam) hOm hfix
  have hexp1 : Real.exp (-m) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hMpos : ∀ σ τ, 0 ≤ tiltKernel (sliceW γ L) β lam σ τ :=
    fun σ τ => (tiltKernel_pos (sliceW γ L) hw β lam hlam σ τ).le
  have hQ1pos : ∀ σ,
      0 < (WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ)))) σ := by
    intro σ
    have h : (WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ)))) σ
        = Real.sqrt (sliceW γ L σ) * 1 := rfl
    rw [h, mul_one]
    exact Real.sqrt_pos.mpr (hw σ)
  obtain ⟨f, hfpos, hfle⟩ :=
    inner_pow_floor (tiltKernel (sliceW γ L) β lam) hMpos Om hOm hT.fix
      (WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ)))) hQ1pos
  have hfne : f ≠ 0 := hfpos.ne'
  have hZeq : ∀ N : ℕ, gibbsPartition (sliceW γ L) β N
      = lam ^ N * ⟪((opOf (tiltKernel (sliceW γ L) β lam)) ^ N)
          (WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ)))),
          WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ)))⟫ :=
    fun N => gibbsPartition_eq_inner_pow (sliceW γ L) hw β lam hlam.ne' N
  have hZpos : ∀ N : ℕ, 0 < gibbsPartition (sliceW γ L) β N := by
    intro N
    rw [hZeq N]
    exact mul_pos (pow_pos hlam N) (lt_of_lt_of_le hfpos (hfle N))
  have hCnonneg : ∀ A B : (Fin (L + 1) → Fin 2) → ℝ,
      0 ≤ 6 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
            * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
            * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖ ^ 2 / f ^ 2 := by
    intro A B
    positivity
  have key : ∀ (N : ℕ) (A B : (Fin (L + 1) → Fin 2) → ℝ),
      |gibbsPathSum (sliceW γ L) β N A B / gibbsPartition (sliceW γ L) β N
          - gibbsPathSum (sliceW γ L) β N A (fun _ => 1)
              / gibbsPartition (sliceW γ L) β N
            * (gibbsPathSum (sliceW γ L) β N (fun _ => 1) B
                / gibbsPartition (sliceW γ L) β N)|
        ≤ 6 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
              * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
              * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖ ^ 2 / f ^ 2
            * Real.exp (-m) ^ N := by
    intro N A B
    have hZp := hZpos N
    have hZne : gibbsPartition (sliceW γ L) β N ≠ 0 := hZp.ne'
    have hnum := gibbs_six_term_bound (sliceW γ L) hw β lam hlam Om hT
      (Real.exp_nonneg _) hexp1 hnorm N A B
    have hid : gibbsPathSum (sliceW γ L) β N A B
            / gibbsPartition (sliceW γ L) β N
          - gibbsPathSum (sliceW γ L) β N A (fun _ => 1)
              / gibbsPartition (sliceW γ L) β N
            * (gibbsPathSum (sliceW γ L) β N (fun _ => 1) B
                / gibbsPartition (sliceW γ L) β N)
        = (gibbsPartition (sliceW γ L) β N * gibbsPathSum (sliceW γ L) β N A B
            - gibbsPathSum (sliceW γ L) β N A (fun _ => 1)
              * gibbsPathSum (sliceW γ L) β N (fun _ => 1) B)
          / gibbsPartition (sliceW γ L) β N ^ 2 := by
      field_simp <;> ring
    have hpow : lam ^ (2 * N) = (lam ^ N) ^ 2 := by
      rw [two_mul, pow_add, pow_two]
    have hZ2 : lam ^ (2 * N) * f ^ 2
        ≤ gibbsPartition (sliceW γ L) β N ^ 2 := by
      rw [hZeq N, mul_pow, hpow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hfpos.le (hfle N) 2)
        (pow_nonneg (pow_nonneg hlam.le N) 2)
    rw [hid, abs_div, abs_of_pos (pow_pos hZp 2),
      div_le_iff₀ (pow_pos hZp 2)]
    calc |gibbsPartition (sliceW γ L) β N * gibbsPathSum (sliceW γ L) β N A B
            - gibbsPathSum (sliceW γ L) β N A (fun _ => 1)
              * gibbsPathSum (sliceW γ L) β N (fun _ => 1) B|
        ≤ lam ^ (2 * N)
            * (6 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
                * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
                * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖ ^ 2)
            * Real.exp (-m) ^ N := hnum
      _ = 6 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
              * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
              * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖ ^ 2 / f ^ 2
            * Real.exp (-m) ^ N * (lam ^ (2 * N) * f ^ 2) := by
          field_simp <;> ring
      _ ≤ 6 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
              * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
              * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖ ^ 2 / f ^ 2
            * Real.exp (-m) ^ N * gibbsPartition (sliceW γ L) β N ^ 2 :=
          mul_le_mul_of_nonneg_left hZ2 (by positivity)
  exact ⟨hZpos, ⟨fun A B => 6 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
      * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
      * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖ ^ 2 / f ^ 2,
    hCnonneg, key⟩⟩
/-- **THE INFINITE-TIME LIMIT STATE: IT EXISTS, IT IS THE VACUUM STATE, AND IT
DOES NOT DEPEND ON THE FAR-END BOUNDARY OBSERVABLE.**  In the window: ONE
`m > 0` such that for EVERY spatial extent, for every observable `A` and every
STRICTLY POSITIVE boundary observable `B`, the one-point expectation of `A` at
the near end of an `N`-step chain terminated by `B`,
`S_N(A,B)/S_N(1,B)`, sits within `C·e^{-mN}` of
`⟪Ω, QA⟫ / ⟪Ω, Q1⟫` — a quantity in which `B` does not appear.

Three readings, all in the one statement: (i) the limit EXISTS and is approached
exponentially at the volume-uniform rate; (ii) the limit IS the Perron/vacuum
state of the reconstructed transfer operator; (iii) the limit is INDEPENDENT of
the boundary condition imposed at the far end -- boundary-condition independence
in the time direction, at fixed spatial extent.  Dividing is licensed by the
off-diagonal cone floor, which no spectral argument supplies. -/
theorem os_reconstruction_vacuum_state_limit (β γ : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ alpha) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        ∀ (A B : (Fin (L + 1) → Fin 2) → ℝ), (∀ σ, 0 < B σ) →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
            |gibbsPathSum (sliceW γ L) β N A B
                  / gibbsPathSum (sliceW γ L) β N (fun _ => 1) B
                - ⟪vacOf Om, WithLp.toLp 2 (dress (sliceW γ L) A)⟫
                  / ⟪vacOf Om,
                      WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))⟫|
              ≤ C * Real.exp (-m) ^ N := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ halpha0 halpha1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  have hw := sliceW_pos γ L
  have hT : VacuumTransfer (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om) :=
    vacuumTransfer_opOf _ Om (tiltKernel_symm _ β lam) hOm hfix
  have hMpos : ∀ σ τ, 0 ≤ tiltKernel (sliceW γ L) β lam σ τ :=
    fun σ τ => (tiltKernel_pos (sliceW γ L) hw β lam hlam σ τ).le
  have hvac : ∀ σ, 0 < vacOf Om σ := vacOf_pos Om hOm
  have hdressPos : ∀ (F : (Fin (L + 1) → Fin 2) → ℝ), (∀ σ, 0 < F σ) →
      ∀ σ, 0 < (WithLp.toLp 2 (dress (sliceW γ L) F)) σ := by
    intro F hF σ
    have h : (WithLp.toLp 2 (dress (sliceW γ L) F)) σ
        = Real.sqrt (sliceW γ L σ) * F σ := rfl
    rw [h]
    exact mul_pos (Real.sqrt_pos.mpr (hw σ)) (hF σ)
  have hQ1pos := hdressPos (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
  have hOm1 : (0 : ℝ)
      < ⟪vacOf Om, WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ)))⟫ := by
    rw [inner_eq_sum]
    exact Finset.sum_pos (fun σ _ => mul_pos (hvac σ) (hQ1pos σ))
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  refine ⟨lam, Om, hlam, hOm, hfix, fun A B hB => ?_⟩
  have hQBpos := hdressPos B hB
  obtain ⟨f, hfpos, hfle⟩ :=
    inner_pow_floor_offdiag (tiltKernel (sliceW γ L) β lam) hMpos Om hOm hT.fix
      (WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ))))
      (WithLp.toLp 2 (dress (sliceW γ L) B)) hQ1pos hQBpos
  refine ⟨2 * ‖WithLp.toLp 2 (dress (sliceW γ L) A)‖
      * ‖WithLp.toLp 2 (dress (sliceW γ L) B)‖
      * ‖WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1))‖
      / (f * ⟪vacOf Om,
          WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ)))⟫),
    div_nonneg (by positivity) (le_of_lt (mul_pos hfpos hOm1)), fun N => ?_⟩
  have hlamN : (lam : ℝ) ^ N ≠ 0 := (pow_pos hlam N).ne'
  have hsymm := hT.pow_symm N
  have hden : f ≤ ⟪WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ))),
      ((opOf (tiltKernel (sliceW γ L) β lam)) ^ N)
        (WithLp.toLp 2 (dress (sliceW γ L) B))⟫ := by
    rw [← hsymm]
    exact hfle N
  have hdenpos : (0 : ℝ) < ⟪WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ))),
      ((opOf (tiltKernel (sliceW γ L) β lam)) ^ N)
        (WithLp.toLp 2 (dress (sliceW γ L) B))⟫ := lt_of_lt_of_le hfpos hden
  have hdenne : (⟪WithLp.toLp 2 (dress (sliceW γ L) (fun _ => (1 : ℝ))),
      ((opOf (tiltKernel (sliceW γ L) β lam)) ^ N)
        (WithLp.toLp 2 (dress (sliceW γ L) B))⟫ : ℝ) ≠ 0 := hdenpos.ne'
  have heq : gibbsPathSum (sliceW γ L) β N A B
        / gibbsPathSum (sliceW γ L) β N (fun _ => 1) B
      = ⟪WithLp.toLp 2 (dress (sliceW γ L) A),
            ((opOf (tiltKernel (sliceW γ L) β lam)) ^ N)
              (WithLp.toLp 2 (dress (sliceW γ L) B))⟫
        / ⟪WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1)),
            ((opOf (tiltKernel (sliceW γ L) β lam)) ^ N)
              (WithLp.toLp 2 (dress (sliceW γ L) B))⟫ := by
    rw [gibbsPathSum_eq_inner_pow (sliceW γ L) hw β lam hlam.ne' N A B,
      gibbsPathSum_eq_inner_pow (sliceW γ L) hw β lam hlam.ne' N (fun _ => 1) B,
      hsymm, hsymm]
    field_simp
  rw [heq]
  exact inner_ratio_approx hT (Real.exp_nonneg _) hnorm
    (WithLp.toLp 2 (dress (sliceW γ L) A))
    (WithLp.toLp 2 (dress (sliceW γ L) (fun _ => 1)))
    (WithLp.toLp 2 (dress (sliceW γ L) B)) N hfpos hden hOm1
/-! ## The ground-state Markov chain — constants uniform in `L` too (pass 24)

The `L`-dependence of the constants above is an artefact of NORMALISATION, not
of the object.  The dressed observables `QA = √w·A` have Euclidean norms that
GROW with the extent, because `‖Q1‖² = ∑_σ w σ` is an unnormalised
partition-function-like quantity; any bound written in those norms therefore
carries an extent-dependent prefactor no matter how sharp the operator estimate
is.  In the correct normalisation the prefactor disappears: the reconstructed
operator IS -- unitarily, by the positive Perron vector -- a reversible Markov
chain, and in its own stationary state the connected correlator is bounded by
the product of the observables' sup norms times `e^{-mN}`, with NO factor
depending on `L` at all. -/

/-- The **ground-state (Doob `h`-transformed) kernel**: the reconstructed
operator conjugated by the positive Perron vector.  It is a stochastic matrix,
and it is reversible for the ground-state measure `Ω²`. -/
noncomputable def groundKernel (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ)
    (Om : (Fin L → Fin 2) → ℝ) (σ τ : Fin L → Fin 2) : ℝ :=
  tiltKernel w β lam σ τ * Om τ / Om σ

theorem groundKernel_nonneg (w : (Fin L → Fin 2) → ℝ) (hw : ∀ σ, 0 < w σ)
    (β lam : ℝ) (hlam : 0 < lam) (Om : (Fin L → Fin 2) → ℝ)
    (hOm : ∀ σ, 0 < Om σ) (σ τ : Fin L → Fin 2) :
    0 ≤ groundKernel w β lam Om σ τ :=
  le_of_lt (div_pos (mul_pos (tiltKernel_pos w hw β lam hlam σ τ) (hOm τ))
    (hOm σ))

/-- **It is stochastic**: the rows sum to one, because `Ω` is the fixed
vector. -/
theorem groundKernel_row_sum (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ)
    (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (hfix : ∀ σ, ∑ τ, tiltKernel w β lam σ τ * Om τ = Om σ) (σ : Fin L → Fin 2) :
    ∑ τ, groundKernel w β lam Om σ τ = 1 := by
  have h : ∑ τ, groundKernel w β lam Om σ τ
      = (∑ τ, tiltKernel w β lam σ τ * Om τ) / Om σ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun τ _ => rfl
  rw [h, hfix σ, div_self (hOm σ).ne']

/-- **It is reversible for `Ω²`** — detailed balance, from the symmetry of the
tilted kernel. -/
theorem groundKernel_reversible (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ)
    (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ) (σ τ : Fin L → Fin 2) :
    Om σ ^ 2 * groundKernel w β lam Om σ τ
      = Om τ ^ 2 * groundKernel w β lam Om τ σ := by
  show Om σ ^ 2 * (tiltKernel w β lam σ τ * Om τ / Om σ)
      = Om τ ^ 2 * (tiltKernel w β lam τ σ * Om σ / Om τ)
  rw [tiltKernel_symm w β lam τ σ]
  have h1 : Om σ ≠ 0 := (hOm σ).ne'
  have h2 : Om τ ≠ 0 := (hOm τ).ne'
  field_simp

/-- The unitary `U` from the ground-state picture to the Euclidean one:
multiplication by the unit vacuum. -/
noncomputable def dressVac (Om : (Fin L → Fin 2) → ℝ)
    (f : (Fin L → Fin 2) → ℝ) : EuclideanSpace ℝ (Fin L → Fin 2) :=
  WithLp.toLp 2 fun σ => vacOf Om σ * f σ

/-- The ground-state measure is a probability measure. -/
theorem sum_vacOf_sq (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ) :
    ∑ σ, vacOf Om σ * vacOf Om σ = 1 := by
  have h : (⟪vacOf Om, vacOf Om⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, vacOf_norm Om hOm]
    norm_num
  rw [← h, inner_eq_sum]

/-- **`U` is a contraction for the sup norm**: a bounded observable is carried
to a Euclidean vector of at most that norm.  This is where the extent
disappears -- the vacuum is a UNIT vector, so no partition function is left
over. -/
theorem norm_dressVac_le (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (f : (Fin L → Fin 2) → ℝ) {K : ℝ} (hK : 0 ≤ K) (hf : ∀ σ, |f σ| ≤ K) :
    ‖dressVac Om f‖ ≤ K := by
  have hsq : ‖dressVac Om f‖ ^ 2 ≤ K ^ 2 := by
    have h1 : (⟪dressVac Om f, dressVac Om f⟫ : ℝ)
        = ∑ σ, (vacOf Om σ * f σ) * (vacOf Om σ * f σ) := inner_eq_sum _ _
    rw [← real_inner_self_eq_norm_sq, h1]
    calc ∑ σ, (vacOf Om σ * f σ) * (vacOf Om σ * f σ)
        ≤ ∑ σ, K ^ 2 * (vacOf Om σ * vacOf Om σ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hfs : f σ * f σ ≤ K * K := by
            have hb := abs_le.mp (hf σ)
            nlinarith [hb.1, hb.2]
          calc (vacOf Om σ * f σ) * (vacOf Om σ * f σ)
              = (vacOf Om σ * vacOf Om σ) * (f σ * f σ) := by ring
            _ ≤ (vacOf Om σ * vacOf Om σ) * (K * K) :=
                mul_le_mul_of_nonneg_left hfs (mul_self_nonneg _)
            _ = K ^ 2 * (vacOf Om σ * vacOf Om σ) := by ring
      _ = K ^ 2 * ∑ σ, vacOf Om σ * vacOf Om σ := by rw [Finset.mul_sum]
      _ = K ^ 2 := by rw [sum_vacOf_sq Om hOm, mul_one]
  nlinarith [norm_nonneg (dressVac Om f), hK, hsq]

/-- The vacuum pairing IS the ground-state expectation. -/
theorem inner_vac_dressVac (Om f : (Fin L → Fin 2) → ℝ) :
    (⟪vacOf Om, dressVac Om f⟫ : ℝ)
      = ∑ σ, (vacOf Om σ * vacOf Om σ) * f σ := by
  rw [inner_eq_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  show vacOf Om σ * (vacOf Om σ * f σ) = (vacOf Om σ * vacOf Om σ) * f σ
  ring

/-- **The intertwining**: the reconstructed operator on a dressed observable is
the dressing of the Markov step.  The normalisation of the vacuum cancels
between the two ends. -/
theorem opOf_dressVac (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ)
    (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (g : (Fin L → Fin 2) → ℝ) :
    opOf (tiltKernel w β lam) (dressVac Om g)
      = dressVac Om (act (fun a b => groundKernel w β lam Om a b) g) := by
  have hS : (0 : ℝ) < ∑ y, Om y * Om y :=
    Finset.sum_pos (fun y _ => mul_pos (hOm y) (hOm y))
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  have hsne : Real.sqrt (∑ y, Om y * Om y) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  refine PiLp.ext fun σ => ?_
  rw [opOf_apply]
  show ∑ τ, tiltKernel w β lam σ τ * (vacOf Om τ * g τ)
      = vacOf Om σ * ∑ τ, groundKernel w β lam Om σ τ * g τ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show tiltKernel w β lam σ τ * (vacOf Om τ * g τ)
      = vacOf Om σ * (tiltKernel w β lam σ τ * Om τ / Om σ * g τ)
  have hvσ : vacOf Om σ = Om σ / Real.sqrt (∑ y, Om y * Om y) := rfl
  have hvτ : vacOf Om τ = Om τ / Real.sqrt (∑ y, Om y * Om y) := rfl
  have hne : Om σ ≠ 0 := (hOm σ).ne'
  rw [hvσ, hvτ]
  field_simp

/-- The intertwining, iterated. -/
theorem opOf_pow_dressVac (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ)
    (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ) (n : ℕ)
    (g : (Fin L → Fin 2) → ℝ) :
    ((opOf (tiltKernel w β lam)) ^ n) (dressVac Om g)
      = dressVac Om ((act (fun a b => groundKernel w β lam Om a b))^[n] g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, opOf_dressVac w β lam Om hOm g,
        ih, Function.iterate_succ_apply]

/-- The `N`-step ground-state correlator IS a matrix element of the
reconstructed operator's powers. -/
theorem inner_dressVac_pow (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ)
    (Om : (Fin L → Fin 2) → ℝ) (hOm : ∀ σ, 0 < Om σ)
    (f g : (Fin L → Fin 2) → ℝ) (N : ℕ) :
    (⟪dressVac Om f,
        ((opOf (tiltKernel w β lam)) ^ N) (dressVac Om g)⟫ : ℝ)
      = ∑ σ, (vacOf Om σ * vacOf Om σ)
          * (f σ * ((act (fun a b => groundKernel w β lam Om a b))^[N] g) σ) := by
  rw [opOf_pow_dressVac w β lam Om hOm N g, inner_eq_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  show vacOf Om σ * f σ
      * (vacOf Om σ * ((act (fun a b => groundKernel w β lam Om a b))^[N] g) σ)
    = (vacOf Om σ * vacOf Om σ)
      * (f σ * ((act (fun a b => groundKernel w β lam Om a b))^[N] g) σ)
  ring

/-- **CLUSTERING WITH A CONSTANT UNIFORM IN THE SPATIAL EXTENT.**  In the
window: ONE `m > 0` such that for EVERY spatial extent the reconstructed
dynamics is a reversible Markov chain (nonnegative, stochastic, detailed
balance for `Ω²`), and in ITS OWN stationary state the connected `N`-step
correlator of any two bounded observables obeys
`|E[f·PᴺG] − E[f]E[g]| ≤ Kf·Kg·e^{-mN}`, where `Kf, Kg` are sup bounds for the
observables.  There is NO factor depending on `L`: the quantifier order is
`∃ m, ∀ L, ∀ f g N`, with the constant `Kf·Kg` supplied by the observables
alone.  This is the same gap as before, read in the normalisation that does
not smuggle a partition function into the constant. -/
theorem os_reconstruction_ground_state_clustering (β γ : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ alpha) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        (∀ σ τ, 0 ≤ groundKernel (sliceW γ L) β lam Om σ τ) ∧
        (∀ σ, ∑ τ, groundKernel (sliceW γ L) β lam Om σ τ = 1) ∧
        (∀ σ τ, Om σ ^ 2 * groundKernel (sliceW γ L) β lam Om σ τ
            = Om τ ^ 2 * groundKernel (sliceW γ L) β lam Om τ σ) ∧
        (∑ σ, vacOf Om σ * vacOf Om σ = 1) ∧
        (∀ (f g : (Fin (L + 1) → Fin 2) → ℝ) (Kf Kg : ℝ),
          0 ≤ Kf → 0 ≤ Kg → (∀ σ, |f σ| ≤ Kf) → (∀ σ, |g σ| ≤ Kg) →
          ∀ N : ℕ,
            |∑ σ, (vacOf Om σ * vacOf Om σ)
                  * (f σ * ((act (fun a b =>
                      groundKernel (sliceW γ L) β lam Om a b))^[N] g) σ)
              - (∑ σ, (vacOf Om σ * vacOf Om σ) * f σ)
                * (∑ σ, (vacOf Om σ * vacOf Om σ) * g σ)|
              ≤ Kf * Kg * Real.exp (-m) ^ N) := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ halpha0 halpha1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  have hw := sliceW_pos γ L
  have hT : VacuumTransfer (opOf (tiltKernel (sliceW γ L) β lam)) (vacOf Om) :=
    vacuumTransfer_opOf _ Om (tiltKernel_symm _ β lam) hOm hfix
  refine ⟨lam, Om, hlam, hOm, hfix,
    fun σ τ => groundKernel_nonneg (sliceW γ L) hw β lam hlam Om hOm σ τ,
    fun σ => groundKernel_row_sum (sliceW γ L) β lam Om hOm hfix σ,
    fun σ τ => groundKernel_reversible (sliceW γ L) β lam Om hOm σ τ,
    sum_vacOf_sq Om hOm, fun f g Kf Kg hKf hKg hf hg N => ?_⟩
  have hmix := mixed_connCorr_bound hT (Real.exp_nonneg _) hnorm
    (dressVac Om f) (dressVac Om g) N
  rw [inner_dressVac_pow (sliceW γ L) β lam Om hOm f g N,
    inner_vac_dressVac Om f, inner_vac_dressVac Om g] at hmix
  refine hmix.trans ?_
  have hnf := norm_dressVac_le Om hOm f hKf hf
  have hng := norm_dressVac_le Om hOm g hKg hg
  have hstep : ‖dressVac Om f‖ * ‖dressVac Om g‖ ≤ Kf * Kg :=
    mul_le_mul hnf hng (norm_nonneg _) hKf
  exact mul_le_mul_of_nonneg_right hstep (pow_nonneg (Real.exp_nonneg _) N)
end YangMills.OS
