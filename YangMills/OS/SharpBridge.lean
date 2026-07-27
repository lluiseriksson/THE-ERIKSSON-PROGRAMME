/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-1c: THE OPERATOR BRIDGE IN ITS SHARP FORM, one self-contained chain.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 1 / AMENDMENT 2.
-/

import Mathlib
import YangMills.OS.DenseClustering

/-!
# O-1c — the sharp bridge, in the bridge's own objects

## Why this module exists

O-1 (`TransferGap.lean`) states the operator bridge over a **real** Hilbert
space and pays for its dense-family version with a uniformly quadratic constant.
O-1b (`DenseClustering.lean`) removes that hypothesis entirely, but lives over a
**complex** Hilbert space, because Mathlib's real continuous functional calculus
is derived from the complex one and so is unavailable for operators on a real
space.  The two therefore did not compose: the sharp theorem was stated about a
bare self-adjoint operator, not about a transfer operator with a vacuum.

This module closes that.  It rebuilds the bridge's objects — vacuum projection,
projected transfer operator, connected two-point function — over ℂ, and proves
the bridge **in its sharp form**:

> `‖T − |Ω⟩⟨Ω|‖ ≤ r`  ⟺  the connected two-point function decays at rate `r` on
> some family of observables whose span is dense, each observable carrying its
> **own** finite constant.

No relation between the constants is assumed, so `C = e^{c·support}` — the shape
of the repository's area-law constant — is admissible.  That is the whole point
of Amendment 1, now stated in the objects a physical application would use.

## What is still open, said plainly

The ℝ↔ℂ bridge is **not** proved: Mathlib has no complexification of a real
inner-product space (there is no `Complexification` anywhere under
`Mathlib/Analysis/`), and building one is a Mathlib-sized contribution, not a
step of this lane.  O-1 therefore remains the ℝ statement and this module the ℂ
statement; the sharp dense-family form is available over ℂ only.  This is a
TOOLING gap, not a mathematical one, and it is recorded rather than glossed.

Nothing here constructs an Osterwalder–Seiler Hilbert space, proves reflection
positivity, or identifies a Euclidean correlator with a matrix element.  Those
are O-2 and OPEN.  No claim about Yang–Mills, the continuum limit, or Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The objects, over ℂ -/

/-- The rank-one projection onto the vacuum line, complex version. -/
noncomputable def vacuumProjectionC (Ω : H) : H →L[ℂ] H :=
  (innerSL ℂ Ω).smulRight Ω

@[simp] theorem vacuumProjectionC_apply (Ω v : H) :
    vacuumProjectionC Ω v = (⟪Ω, v⟫_ℂ) • Ω := rfl

/-- The vacuum-projected transfer operator `T − |Ω⟩⟨Ω|`, complex version. -/
noncomputable def projectedTransferC (T : H →L[ℂ] H) (Ω : H) : H →L[ℂ] H :=
  T - vacuumProjectionC Ω

@[simp] theorem projectedTransferC_apply (T : H →L[ℂ] H) (Ω v : H) :
    projectedTransferC T Ω v = T v - (⟪Ω, v⟫_ℂ) • Ω := rfl

/-- The connected (truncated) two-point function at Euclidean time `n`. -/
noncomputable def connCorrC (T : H →L[ℂ] H) (Ω : H) (v : H) (n : ℕ) : ℂ :=
  ⟪v, (T ^ n) v⟫_ℂ - ⟪v, Ω⟫_ℂ * ⟪Ω, v⟫_ℂ

/-- A transfer operator with a vacuum, complex version. -/
structure VacuumTransferC (T : H →L[ℂ] H) (Ω : H) : Prop where
  /-- Self-adjointness, in Mathlib's `star`-form (so the functional calculus applies). -/
  selfAdjoint : IsSelfAdjoint T
  /-- The vacuum is a unit vector. -/
  unit : ‖Ω‖ = 1
  /-- The vacuum is fixed. -/
  fix : T Ω = Ω

namespace VacuumTransferC

variable {T : H →L[ℂ] H} {Ω : H}

theorem inner_vacuum_self (hT : VacuumTransferC T Ω) : (⟪Ω, Ω⟫_ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hT.unit]
  norm_num

theorem symm (hT : VacuumTransferC T Ω) (v w : H) : ⟪T v, w⟫_ℂ = ⟪v, T w⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT.selfAdjoint) v w

theorem pow_symm (hT : VacuumTransferC T Ω) (n : ℕ) (v w : H) :
    ⟪(T ^ n) v, w⟫_ℂ = ⟪v, (T ^ n) w⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hT.selfAdjoint.pow n)) v w

theorem pow_fix (hT : VacuumTransferC T Ω) (n : ℕ) : (T ^ n) Ω = Ω := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hstep : (T ^ (m + 1)) Ω = T ((T ^ m) Ω) := by rw [pow_succ']; rfl
      rw [hstep, ih, hT.fix]

/-- The vacuum projection is self-adjoint. -/
theorem vacuumProjectionC_selfAdjoint (Ω : H) : IsSelfAdjoint (vacuumProjectionC (H := H) Ω) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  show ⟪(⟪Ω, v⟫_ℂ) • Ω, w⟫_ℂ = ⟪v, (⟪Ω, w⟫_ℂ) • Ω⟫_ℂ
  rw [inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

/-- The projected transfer operator is self-adjoint — this is what lets O-1b's
functional-calculus theorem apply to it. -/
theorem projected_selfAdjoint (hT : VacuumTransferC T Ω) :
    IsSelfAdjoint (projectedTransferC T Ω) := by
  rw [projectedTransferC]
  exact hT.selfAdjoint.sub (vacuumProjectionC_selfAdjoint Ω)

/-- **The structural identity**, complex version: for `n ≥ 1` the powers of the
projected operator subtract exactly the vacuum contribution. -/
theorem projected_pow_succ (hT : VacuumTransferC T Ω) (v : H) (n : ℕ) :
    (projectedTransferC T Ω ^ (n + 1)) v = (T ^ (n + 1)) v - (⟪Ω, v⟫_ℂ) • Ω := by
  induction n with
  | zero => simp [projectedTransferC_apply]
  | succ m ih =>
      have hS : (projectedTransferC T Ω ^ (m + 2)) v
          = projectedTransferC T Ω ((projectedTransferC T Ω ^ (m + 1)) v) := by
        rw [pow_succ']; rfl
      have hT' : (T ^ (m + 2)) v = T ((T ^ (m + 1)) v) := by rw [pow_succ']; rfl
      have horth : (⟪Ω, (T ^ (m + 1)) v - (⟪Ω, v⟫_ℂ) • Ω⟫_ℂ) = 0 := by
        rw [inner_sub_right, inner_smul_right, hT.inner_vacuum_self]
        have hmove : (⟪Ω, (T ^ (m + 1)) v⟫_ℂ) = ⟪(T ^ (m + 1)) Ω, v⟫_ℂ :=
          (hT.pow_symm (m + 1) Ω v).symm
        rw [hmove, hT.pow_fix]
        ring
      rw [hS, ih, hT']
      simp only [projectedTransferC_apply, horth]
      rw [map_sub, map_smul, hT.fix]
      simp

/-- **The connected correlator is a matrix element of the projected operator**,
complex version. -/
theorem connCorrC_eq (hT : VacuumTransferC T Ω) (v : H) (n : ℕ) :
    connCorrC T Ω v (n + 1) = ⟪v, (projectedTransferC T Ω ^ (n + 1)) v⟫_ℂ := by
  rw [hT.projected_pow_succ v n, inner_sub_right, inner_smul_right, connCorrC]
  ring

end VacuumTransferC

/-! ## Even times see the norm -/

/-- For a self-adjoint operator, `‖⟪v, S^{2n} v⟫‖ = ‖Sⁿ v‖²`.  Stated with norms
on both sides on purpose: the complex-valued form
`⟪v, S^{2n} v⟫ = ((‖Sⁿ v‖ : ℂ))²` is true but its two sides carry different
coercion paths (`Complex.ofReal` vs `RCLike.ofReal`) that display identically
and defeat `ring`.  Norms are all the consumers need.

This is the identity that turns a bound on the *correlator* into a bound on the
*orbit*, and hence into membership in `decayDomain`. -/
theorem norm_inner_pow_two_mul_C {S : H →L[ℂ] H} (hS : IsSelfAdjoint S) (n : ℕ) (v : H) :
    ‖(⟪v, (S ^ (2 * n)) v⟫_ℂ)‖ = ‖(S ^ n) v‖ ^ 2 := by
  have hsym : ∀ x y : H, ⟪(S ^ n) x, y⟫_ℂ = ⟪x, (S ^ n) y⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hS.pow n)
  have hsplit : (S ^ (2 * n)) v = (S ^ n) ((S ^ n) v) := by
    rw [two_mul, pow_add]; rfl
  rw [hsplit, ← hsym v ((S ^ n) v), inner_self_eq_norm_sq_to_K]
  simp

/-! ## The sharp bridge -/

/-- Clustering of the connected correlator at a single observable puts that
observable in the decay domain of the projected operator. -/
theorem mem_decayDomain_of_connCorrC {T : H →L[ℂ] H} {Ω : H} (hT : VacuumTransferC T Ω)
    {r : ℝ} (hr : 0 ≤ r) {v : H} {C : ℝ}
    (hC : ∀ n : ℕ, ‖connCorrC T Ω v n‖ ≤ C * r ^ n) :
    v ∈ decayDomain (projectedTransferC T Ω) r := by
  set S := projectedTransferC T Ω with hSdef
  have hSsa : IsSelfAdjoint S := hT.projected_selfAdjoint
  refine ⟨max (Real.sqrt (max C 0)) ‖v‖, fun n => ?_⟩
  cases n with
  | zero =>
      simp
  | succ m =>
      -- `‖S^{m+1} v‖² = |connCorr … (2(m+1))| ≤ C r^{2(m+1)}`
      have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      have h2 := hC (2 * (m + 1))
      rw [hidx, hT.connCorrC_eq v (2 * m + 1), ← hidx] at h2
      rw [norm_inner_pow_two_mul_C hSsa (m + 1) v] at h2
      have hnn : (0 : ℝ) ≤ max C 0 := le_max_right C 0
      have hbnd : ‖(S ^ (m + 1)) v‖ ^ 2
          ≤ (Real.sqrt (max C 0) * r ^ (m + 1)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hnn, ← pow_mul, mul_comm (m + 1) 2]
        exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hr _))
      have hstep : ‖(S ^ (m + 1)) v‖ ≤ Real.sqrt (max C 0) * r ^ (m + 1) := by
        by_contra hc
        push_neg at hc
        nlinarith [norm_nonneg ((S ^ (m + 1)) v), Real.sqrt_nonneg (max C 0),
          pow_nonneg hr (m + 1),
          mul_nonneg (Real.sqrt_nonneg (max C 0)) (pow_nonneg hr (m + 1))]
      exact hstep.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr _))

/-- **Gap ⟹ clustering**, complex version.  The constant `2‖v‖²` is deliberately
crude: the forward direction of the bridge only has to produce *some* finite
constant, so the `n = 0` term is bounded by the triangle inequality rather than
by an exact identity for `⟪v,Ω⟫⟪Ω,v⟫`. -/
theorem connCorrC_le_of_gap {T : H →L[ℂ] H} {Ω : H} (hT : VacuumTransferC T Ω)
    {r : ℝ} (hgap : ‖projectedTransferC T Ω‖ ≤ r) (v : H) (n : ℕ) :
    ‖connCorrC T Ω v n‖ ≤ (2 * ‖v‖ ^ 2) * r ^ n := by
  have hr : 0 ≤ r := le_trans (norm_nonneg _) hgap
  have hcs : ‖(⟪Ω, v⟫_ℂ)‖ ≤ ‖v‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) Ω v
    rwa [hT.unit, one_mul] at h
  have hcs' : ‖(⟪v, Ω⟫_ℂ)‖ ≤ ‖v‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) v Ω
    rwa [hT.unit, mul_one] at h
  cases n with
  | zero =>
      rw [connCorrC, pow_zero, pow_zero, mul_one]
      simp only [ContinuousLinearMap.one_apply]
      rw [inner_self_eq_norm_sq_to_K]
      calc ‖((‖v‖ : ℂ) ^ 2) - ⟪v, Ω⟫_ℂ * ⟪Ω, v⟫_ℂ‖
          ≤ ‖((‖v‖ : ℂ) ^ 2)‖ + ‖⟪v, Ω⟫_ℂ * ⟪Ω, v⟫_ℂ‖ := norm_sub_le _ _
        _ = ‖v‖ ^ 2 + ‖(⟪v, Ω⟫_ℂ)‖ * ‖(⟪Ω, v⟫_ℂ)‖ := by
            rw [norm_mul]
            congr 1
            simp
        _ ≤ ‖v‖ ^ 2 + ‖v‖ * ‖v‖ := by
            have hmul := mul_le_mul hcs' hcs (norm_nonneg _) (norm_nonneg v)
            linarith
        _ = 2 * ‖v‖ ^ 2 := by ring
  | succ m =>
      rw [hT.connCorrC_eq v m]
      set S := projectedTransferC T Ω
      have hstep : ‖(S ^ (m + 1)) v‖ ≤ r ^ (m + 1) * ‖v‖ := by
        calc ‖(S ^ (m + 1)) v‖ ≤ ‖S ^ (m + 1)‖ * ‖v‖ := (S ^ (m + 1)).le_opNorm v
          _ ≤ ‖S‖ ^ (m + 1) * ‖v‖ :=
              mul_le_mul_of_nonneg_right (norm_pow_le' S (Nat.succ_pos m)) (norm_nonneg v)
          _ ≤ r ^ (m + 1) * ‖v‖ :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg S) hgap (m + 1)) (norm_nonneg v)
      calc ‖(⟪v, (S ^ (m + 1)) v⟫_ℂ)‖ ≤ ‖v‖ * ‖(S ^ (m + 1)) v‖ :=
            norm_inner_le_norm (𝕜 := ℂ) v _
        _ ≤ ‖v‖ * (r ^ (m + 1) * ‖v‖) := mul_le_mul_of_nonneg_left hstep (norm_nonneg v)
        _ = ‖v‖ ^ 2 * r ^ (m + 1) := by ring
        _ ≤ (2 * ‖v‖ ^ 2) * r ^ (m + 1) := by
            have : ‖v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
            exact mul_le_mul_of_nonneg_right this (pow_nonneg hr _)

/-- **O-1c — THE SHARP BRIDGE.**  For a transfer operator with a fixed unit
vacuum, the spectral-gap bound `‖T − |Ω⟩⟨Ω|‖ ≤ r` is **equivalent** to
exponential decay of the connected two-point function on some family of
observables whose span is dense — each observable carrying its **own** finite
constant, with no relation assumed between them.

This is the theorem an application would consume, and it is the sharp form: a
constant of the shape `e^{c·support}` is perfectly admissible, which is exactly
what AMENDMENT 1 retracted the opposite of. -/
theorem sharp_clustering_iff_gap [Nontrivial H] {T : H →L[ℂ] H} {Ω : H}
    (hT : VacuumTransferC T Ω) {r : ℝ} (hr : 0 ≤ r) :
    ‖projectedTransferC T Ω‖ ≤ r ↔
      ∃ D : Set H, Dense ((Submodule.span ℂ D : Submodule ℂ H) : Set H) ∧
        ∀ v ∈ D, ∃ C : ℝ, ∀ n : ℕ, ‖connCorrC T Ω v n‖ ≤ C * r ^ n := by
  constructor
  · intro hgap
    refine ⟨Set.univ, ?_, fun v _ => ⟨2 * ‖v‖ ^ 2, fun n => connCorrC_le_of_gap hT hgap v n⟩⟩
    rw [Submodule.span_univ]
    simp [dense_iff_closure_eq]
  · rintro ⟨D, hspan, hD⟩
    refine norm_le_of_span_dense_decay hT.projected_selfAdjoint hr D hspan ?_
    intro v hv
    obtain ⟨C, hC⟩ := hD v hv
    exact mem_decayDomain_of_connCorrC hT hr hC

/-- **Volume-uniformity, sharp form.**  A family of transfer operators — one per
finite volume, each on its own Hilbert space — whose connected correlators decay
at a *common* rate `r < 1` on spanning families with **arbitrary** per-observable
constants has a *common* strictly positive mass `m = −log r`. -/
theorem volumeUniform_sharp_gap {ι : Type*} {Hs : ι → Type*}
    [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    [∀ i, CompleteSpace (Hs i)] [∀ i, Nontrivial (Hs i)]
    (T : ∀ i, Hs i →L[ℂ] Hs i) (Ω : ∀ i, Hs i)
    (hT : ∀ i, VacuumTransferC (T i) (Ω i))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (D : ∀ i, Set (Hs i))
    (hspan : ∀ i, Dense ((Submodule.span ℂ (D i) : Submodule ℂ (Hs i)) : Set (Hs i)))
    (hD : ∀ i, ∀ v ∈ D i, ∃ C : ℝ, ∀ n : ℕ, ‖connCorrC (T i) (Ω i) v n‖ ≤ C * r ^ n) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, ‖projectedTransferC (T i) (Ω i)‖ ≤ Real.exp (-m) := by
  refine ⟨-Real.log r, neg_pos.mpr (Real.log_neg hr0 hr1), fun i => ?_⟩
  rw [show Real.exp (-(-Real.log r)) = r by rw [neg_neg, Real.exp_log hr0]]
  exact (sharp_clustering_iff_gap (hT i) hr0.le).mpr ⟨D i, hspan i, hD i⟩

/-! ## Non-vacuity, over ℂ -/

/-- **Non-vacuity witness.**  With a unit vector orthogonal to the vacuum — i.e.
a nonzero fluctuation sector — the sharp bridge has an inhabitant with a
strictly positive gap and a **nonzero** projected operator.  So no statement
above is satisfied only by the degenerate one-dimensional instance. -/
theorem exists_vacuumTransferC_gap {Ω w : H} (hΩ : ‖Ω‖ = 1) (hw : ‖w‖ = 1)
    (hperp : (⟪Ω, w⟫_ℂ) = 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ T : H →L[ℂ] H, VacuumTransferC T Ω ∧
      ‖projectedTransferC T Ω‖ = r ∧ projectedTransferC T Ω ≠ 0 ∧
      0 < -Real.log r := by
  have hΩΩ : (⟪Ω, Ω⟫_ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  -- `Q := 1 − |Ω⟩⟨Ω|` is an idempotent self-adjoint operator, hence a contraction
  have hPsa : IsSelfAdjoint (vacuumProjectionC (H := H) Ω) :=
    VacuumTransferC.vacuumProjectionC_selfAdjoint Ω
  have hidem : ∀ v : H, vacuumProjectionC (H := H) Ω (vacuumProjectionC (H := H) Ω v)
      = vacuumProjectionC (H := H) Ω v := by
    intro v
    simp only [vacuumProjectionC_apply, inner_smul_right, hΩΩ]
    rw [mul_one]
  have hone : IsSelfAdjoint (1 : H →L[ℂ] H) := by simp [IsSelfAdjoint]
  set Q : H →L[ℂ] H := 1 - vacuumProjectionC (H := H) Ω with hQdef
  have hQsa : IsSelfAdjoint Q := by
    rw [hQdef]
    exact hone.sub hPsa
  have hQsym : ∀ x y : H, ⟪Q x, y⟫_ℂ = ⟪x, Q y⟫_ℂ := fun x y =>
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQsa) x y
  have hQidem : ∀ v : H, Q (Q v) = Q v := by
    intro v
    simp only [hQdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub]
    rw [hidem v]
    abel
  have hQle : ‖Q‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    have hsym : ⟪Q v, Q v⟫_ℂ = ⟪v, Q v⟫_ℂ := by
      rw [hQsym v (Q v), hQidem v]
    have hnn : ‖Q v‖ ^ 2 ≤ ‖v‖ * ‖Q v‖ := by
      have h1 : ‖(⟪Q v, Q v⟫_ℂ)‖ = ‖Q v‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]; simp
      rw [← h1, hsym]
      exact norm_inner_le_norm (𝕜 := ℂ) v (Q v)
    rw [one_mul]
    rcases eq_or_lt_of_le (norm_nonneg (Q v)) with h | h
    · rw [← h]; exact norm_nonneg v
    · nlinarith
  have hQw : Q w = w := by
    simp [hQdef, vacuumProjectionC_apply, hperp]
  have hQge : (1 : ℝ) ≤ ‖Q‖ := by
    have := Q.le_opNorm w
    rw [hQw, hw, mul_one] at this
    exact this
  have hQnorm : ‖Q‖ = 1 := le_antisymm hQle hQge
  -- every scalar is ℂ: mixing ℝ- and ℂ-smul is what `module`/`match_scalars` cannot do
  have hrsa : IsSelfAdjoint ((r : ℂ)) := Complex.conj_ofReal r
  have honeC : IsSelfAdjoint ((1 : ℂ)) := by simp [IsSelfAdjoint]
  have hEq : projectedTransferC ((r : ℂ) • (1 : H →L[ℂ] H)
      + ((1 : ℂ) - (r : ℂ)) • vacuumProjectionC Ω) Ω = (r : ℂ) • Q := by
    rw [projectedTransferC, hQdef]
    module
  refine ⟨(r : ℂ) • (1 : H →L[ℂ] H) + ((1 : ℂ) - (r : ℂ)) • vacuumProjectionC Ω,
    ?_, ?_, ?_, ?_⟩
  · refine ⟨(hrsa.smul hone).add ((honeC.sub hrsa).smul hPsa), hΩ, ?_⟩
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, vacuumProjectionC_apply, hΩΩ, one_smul]
    have hsum : (r : ℂ) + ((1 : ℂ) - (r : ℂ)) = 1 := by ring
    rw [← add_smul, hsum, one_smul]
  · rw [hEq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hQnorm, mul_one]
  · rw [hEq]
    intro h0
    have happ : ((r : ℂ) • Q) w = (r : ℂ) • w := by rw [ContinuousLinearMap.smul_apply, hQw]
    rw [h0] at happ
    simp only [ContinuousLinearMap.zero_apply] at happ
    have hne : (r : ℂ) • w ≠ (0 : H) := by
      refine smul_ne_zero ?_ ?_
      · simpa using ne_of_gt hr0
      · intro hw0
        rw [hw0, norm_zero] at hw
        exact absurd hw (by norm_num)
    exact hne happ.symm
  · exact neg_pos.mpr (Real.log_neg hr0 hr1)

/-- **Non-vacuity, concrete.**  The two-dimensional complex Euclidean instance
discharges every hypothesis of `exists_vacuumTransferC_gap`. -/
theorem euclidean_two_dim_vacuumTransferC_gap {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ (T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
      VacuumTransferC T (EuclideanSpace.single 0 1) ∧
      ‖projectedTransferC T (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))‖ = r ∧
      projectedTransferC T (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) ≠ 0 ∧
      0 < -Real.log r := by
  have hΩ : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℂ))‖ = 1 := by
    rw [EuclideanSpace.norm_single]; norm_num
  have hw : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℂ))‖ = 1 := by
    rw [EuclideanSpace.norm_single]; norm_num
  have hperp : (⟪(EuclideanSpace.single (0 : Fin 2) (1 : ℂ)),
      (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))⟫_ℂ) = 0 := by
    simp [PiLp.inner_apply, EuclideanSpace.single_apply]
  exact exists_vacuumTransferC_gap hΩ hw hperp hr0 hr1

end YangMills.OS
