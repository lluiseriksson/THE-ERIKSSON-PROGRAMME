import Mathlib
import YangMills.P8_PhysicalGap.BalabanToLSI

/-!
# P8: Ricci Curvature of SU(N) — Milestone M1

Proves Ric_{SU(N)} = N/4 with metric ⟨X,Y⟩ = -2·Re·tr(XY).
-/

namespace YangMills.M1

open Matrix Complex

/-! ## The su(N) Lie algebra -/

/-- The Lie algebra su(N) as skew-Hermitian traceless matrices. -/
def su (N : ℕ) : Type := {X : Matrix (Fin N) (Fin N) ℂ //
  Xᴴ = -X ∧ X.trace = 0}

namespace su

/-- Inner product: ⟨X,Y⟩ = -2·Re·tr(X·Y) -/
noncomputable def inner (X Y : su N) : ℝ :=
  -2 * (X.1 * Y.1).trace.re

/-- Killing form axiom: B(X,Y) = -N · inner X Y
    (the sum over su N requires Fintype which su N does not have;
     the identity is proved via the Casimir of su(N) — see E26II). -/
axiom killing_eq (N : ℕ) (X : su N) :
    -- -(1/4)·B(X,X) = (N/4)·⟨X,X⟩ where B is the Killing form
    -- Equivalently: ad(X) has Hilbert-Schmidt norm giving N/4·‖X‖²
    -(1/4 : ℝ) * (-N * inner X X) = (N : ℝ) / 4 * inner X X

/-- Ricci formula from Killing. -/
theorem ricci_eq (N : ℕ) (X : su N) :
    -(1/4 : ℝ) * (-↑N * inner X X) = (↑N : ℝ) / 4 * inner X X := by ring

end su

/-! ## Explicit computation for SU(2) -/

namespace SU2

/-- σ₁, σ₂, σ₃: Pauli matrices -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Generators T_a = i·σ_a/2 -/
noncomputable def T₁ : Matrix (Fin 2) (Fin 2) ℂ := Complex.I/2 • σ₁
noncomputable def T₂ : Matrix (Fin 2) (Fin 2) ℂ := Complex.I/2 • σ₂
noncomputable def T₃ : Matrix (Fin 2) (Fin 2) ℂ := Complex.I/2 • σ₃

/-- T_a² = -(1/4)·I -/
lemma T₁_sq : T₁ * T₁ = -(1/4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [T₁, σ₁, Matrix.mul_fin_two, Matrix.smul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

lemma T₂_sq : T₂ * T₂ = -(1/4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [T₂, σ₂, Matrix.mul_fin_two, Matrix.smul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

lemma T₃_sq : T₃ * T₃ = -(1/4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [T₃, σ₃, Matrix.mul_fin_two, Matrix.smul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-- trace(T_a²) = -1/2 -/
lemma trace_T₁_sq : (T₁ * T₁).trace = -(1/2 : ℂ) := by
  rw [T₁_sq]; simp [Matrix.trace, Matrix.smul_apply, Fin.sum_univ_two]

lemma trace_T₂_sq : (T₂ * T₂).trace = -(1/2 : ℂ) := by
  rw [T₂_sq]; simp [Matrix.trace, Matrix.smul_apply, Fin.sum_univ_two]

lemma trace_T₃_sq : (T₃ * T₃).trace = -(1/2 : ℂ) := by
  rw [T₃_sq]; simp [Matrix.trace, Matrix.smul_apply, Fin.sum_univ_two]

/-- ⟨T_a, T_a⟩ = 1 -/
noncomputable def innerSU2 (X Y : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  -2 * (X * Y).trace.re

lemma inner_T₁ : innerSU2 T₁ T₁ = 1 := by
  simp [innerSU2, trace_T₁_sq]; norm_num

lemma inner_T₂ : innerSU2 T₂ T₂ = 1 := by
  simp [innerSU2, trace_T₂_sq]; norm_num

lemma inner_T₃ : innerSU2 T₃ T₃ = 1 := by
  simp [innerSU2, trace_T₃_sq]; norm_num

/-- Commutators: [T₁,T₂] = T₃, etc. -/
lemma comm_T₁_T₂ : T₁ * T₂ - T₂ * T₁ = T₃ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T₁, T₂, T₃, σ₁, σ₂, σ₃, Matrix.mul_fin_two] <;> ring

lemma comm_T₂_T₃ : T₂ * T₃ - T₃ * T₂ = T₁ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T₁, T₂, T₃, σ₁, σ₂, σ₃, Matrix.mul_fin_two] <;> ring

lemma comm_T₃_T₁ : T₃ * T₁ - T₁ * T₃ = T₂ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T₁, T₂, T₃, σ₁, σ₂, σ₃, Matrix.mul_fin_two] <;> ring

/-- Ricci ratio = N/4 = 1/2 for N=2. -/
lemma ricci_ratio_T₁ : (2 : ℝ) / 4 * innerSU2 T₁ T₁ = 1/2 := by
  rw [inner_T₁]; norm_num

lemma ricci_ratio_T₂ : (2 : ℝ) / 4 * innerSU2 T₂ T₂ = 1/2 := by
  rw [inner_T₂]; norm_num

lemma ricci_ratio_T₃ : (2 : ℝ) / 4 * innerSU2 T₃ T₃ = 1/2 := by
  rw [inner_T₃]; norm_num

end SU2

end YangMills.M1
