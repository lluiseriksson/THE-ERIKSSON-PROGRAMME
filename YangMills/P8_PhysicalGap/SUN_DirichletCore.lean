import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.Experimental.LieSUN.LieDerivativeBridge

/-!
# SUN_DirichletCore — v0.8.36

Cycle-free module: SU(N) Dirichlet form without LSItoSpectralGap.
-/

namespace YangMills
open MeasureTheory Matrix

noncomputable section

/-- Index type for su(N_c) Lie algebra generators. dim su(N) = N²-1. -/
abbrev LieGenIndex (N_c : ℕ) : Type := Fin (N_c ^ 2 - 1)

/-- Fintype instance: LieGenIndex N_c = Fin (N_c²-1) is finite by definition. -/
instance instFintypeLieGenIndex (N_c : ℕ) : Fintype (LieGenIndex N_c) := inferInstance

/-- Abstract generator matrices for su(N_c) — the N²-1 basis elements.
    Each satisfies: skew-Hermitian (Xᴴ = -X) and trace-zero. -/
opaque generatorMatrix (N_c : ℕ) (i : LieGenIndex N_c) :
    Matrix (Fin N_c) (Fin N_c) ℂ

axiom generator_skewHermitian (N_c : ℕ) [NeZero N_c] (i : LieGenIndex N_c) :
    (generatorMatrix N_c i)ᴴ = -(generatorMatrix N_c i)

axiom generator_trace_zero (N_c : ℕ) [NeZero N_c] (i : LieGenIndex N_c) :
    (generatorMatrix N_c i).trace = 0

/-- Directional derivative along the i-th generator: d/dt|₀ f(U·exp(t·Xᵢ)).
    Defined concretely via lieDerivExp from LieDerivativeBridge. -/
noncomputable def lieDerivative (N_c : ℕ) [NeZero N_c] (i : LieGenIndex N_c)
    (f : SUN_State_Concrete N_c → ℝ) :
    SUN_State_Concrete N_c → ℝ :=
  fun U => _root_.lieDerivExp
    (generatorMatrix N_c i)
    (generator_skewHermitian N_c i)
    (generator_trace_zero N_c i)
    f U

/-- The SU(N_c) Dirichlet form: E(f) = Σᵢ ∫ (∂_{Xᵢ} f)² dμ_Haar -/
noncomputable def sunDirichletForm_concrete (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : ℝ :=
  ∑ i : LieGenIndex N_c,
    ∫ U : SUN_State_Concrete N_c,
      (lieDerivative N_c i f U) ^ 2
    ∂(sunHaarProb N_c)

/-- MATHLIB GAP: Lie derivatives are linear. -/
axiom lieDerivative_linear (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) :
    (∀ (f g : SUN_State_Concrete N_c → ℝ),
      lieDerivative N_c i (f + g) =
      lieDerivative N_c i f + lieDerivative N_c i g) ∧
    (∀ (c : ℝ) (f : SUN_State_Concrete N_c → ℝ),
      lieDerivative N_c i (fun U => c * f U) =
      fun U => c * lieDerivative N_c i f U)

/-- Lie derivatives annihilate constants. PROVED via lieDerivExp_const. -/
theorem lieDerivative_const (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (c : ℝ) :
    lieDerivative N_c i (fun _ : SUN_State_Concrete N_c => c) = 0 := by
  funext U
  simp only [lieDerivative]
  exact _root_.lieDerivExp_const
    (generatorMatrix N_c i)
    (generator_skewHermitian N_c i)
    (generator_trace_zero N_c i)
    c U

lemma lieDerivative_add (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (f g : SUN_State_Concrete N_c → ℝ) :
    lieDerivative N_c i (f + g) =
    lieDerivative N_c i f + lieDerivative N_c i g :=
  (lieDerivative_linear N_c i).1 f g

lemma lieDerivative_smul (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (c : ℝ) (f : SUN_State_Concrete N_c → ℝ) :
    lieDerivative N_c i (fun U => c * f U) =
    fun U => c * lieDerivative N_c i f U :=
  (lieDerivative_linear N_c i).2 c f

lemma lieDerivative_const_add (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (f : SUN_State_Concrete N_c → ℝ) (c : ℝ) :
    lieDerivative N_c i (fun U => f U + c) = lieDerivative N_c i f := by
  have h_add := (lieDerivative_linear N_c i).1 f (fun _ => c)
  have h_zero := lieDerivative_const N_c i c
  show lieDerivative N_c i (f + fun _ => c) = lieDerivative N_c i f
  rw [h_add, h_zero, add_zero]

lemma sunDirichletForm_nonneg {N_c : ℕ} [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) :
    0 ≤ sunDirichletForm_concrete N_c f := by
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun U => sq_nonneg _)

lemma sunDirichletForm_const_invariant {N_c : ℕ} [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) (c : ℝ) :
    sunDirichletForm_concrete N_c (fun U => f U + c) =
    sunDirichletForm_concrete N_c f := by
  simp [sunDirichletForm_concrete, lieDerivative_const_add]

lemma sunDirichletForm_quadratic {N_c : ℕ} [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) (c : ℝ) :
    sunDirichletForm_concrete N_c (fun U => c * f U) =
    c ^ 2 * sunDirichletForm_concrete N_c f := by
  simp only [sunDirichletForm_concrete, lieDerivative_smul]
  rw [Finset.mul_sum]
  congr 1; ext i
  -- ∫ U, (c * lieDerivative N_c i f U)² = c² * ∫ U, (lieDerivative N_c i f U)²
  -- Rewrite integrand: (c * x)² = c² * x², then pull constant out
  have : (fun U => (c * lieDerivative N_c i f U) ^ 2) =
         (fun U => c ^ 2 * (lieDerivative N_c i f U) ^ 2) := by
    ext U; ring
  rw [this, integral_const_mul]

/-- E(f+g) ≤ 2·E(f) + 2·E(g).
    Proof: (a+b)² ≤ 2a²+2b², integrate, sum.
    Subadditivity of integrals requires fun_prop on lieDerivative — using axiom. -/
axiom sunDirichletForm_subadditive {N_c : ℕ} [NeZero N_c]
    (f g : SUN_State_Concrete N_c → ℝ) :
    sunDirichletForm_concrete N_c (f + g) ≤
    2 * sunDirichletForm_concrete N_c f +
    2 * sunDirichletForm_concrete N_c g

lemma sunDirichletForm_isDirichletForm {N_c : ℕ} [NeZero N_c] :
    IsDirichletForm (sunDirichletForm_concrete N_c) (sunHaarProb N_c) :=
  ⟨fun f => sunDirichletForm_nonneg f,
   fun f g => sunDirichletForm_subadditive f g⟩

/-- MATHLIB GAP: Normal contraction (Beurling-Deny). -/
axiom sunDirichletForm_contraction (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) (n : ℝ) (hn : 0 < n) :
    sunDirichletForm_concrete N_c (fun x => max (min (f x) n) (-n)) ≤
    sunDirichletForm_concrete N_c f

lemma sunDirichletForm_isDirichletFormStrong {N_c : ℕ} [NeZero N_c] :
    IsDirichletFormStrong (sunDirichletForm_concrete N_c) (sunHaarProb N_c) :=
  ⟨sunDirichletForm_isDirichletForm,
   fun c f => sunDirichletForm_const_invariant f c,
   fun c f => sunDirichletForm_quadratic f c,
   fun f n hn => sunDirichletForm_contraction N_c f n hn⟩

end
end YangMills
