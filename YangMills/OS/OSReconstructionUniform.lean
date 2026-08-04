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

end YangMills.OS
