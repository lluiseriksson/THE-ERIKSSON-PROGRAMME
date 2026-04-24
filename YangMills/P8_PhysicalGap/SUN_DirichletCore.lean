import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.Experimental.LieSUN.LieDerivReg_v4

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

/-- Directional derivative along the i-th generator via lieDerivExp.
    Now concrete: uses sunGeneratorData for generator matrices. -/
noncomputable def lieDerivative (N_c : ℕ) [NeZero N_c] (i : LieGenIndex N_c)
    (f : SUN_State_Concrete N_c → ℝ) :
    SUN_State_Concrete N_c → ℝ :=
  fun U => lieD' N_c i f U

/-- The SU(N_c) Dirichlet form: E(f) = Σᵢ ∫ (∂_{Xᵢ} f)² dμ_Haar -/
noncomputable def sunDirichletForm_concrete (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : ℝ :=
  ∑ i : LieGenIndex N_c,
    ∫ U : SUN_State_Concrete N_c,
      (lieDerivative N_c i f U) ^ 2
    ∂(sunHaarProb N_c)

/-- Lie derivatives are linear. PROVED via lieD'_add + lieD'_smul. -/
theorem lieDerivative_linear (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) :
    (∀ (f g : SUN_State_Concrete N_c → ℝ),
      lieDerivative N_c i (f + g) =
      lieDerivative N_c i f + lieDerivative N_c i g) ∧
    (∀ (c : ℝ) (f : SUN_State_Concrete N_c → ℝ),
      lieDerivative N_c i (fun U => c * f U) =
      fun U => c * lieDerivative N_c i f U) := by
  constructor
  · intro f g; funext U
    show lieD' N_c i (f + g) U = lieD' N_c i f U + lieD' N_c i g U
    exact lieD'_add N_c i f g U
  · intro c f; funext U
    show lieD' N_c i (fun x => c * f x) U = c * lieD' N_c i f U
    exact lieD'_smul N_c i c f U

/-- Lie derivatives annihilate constants. PROVED via lieD'_const. -/
theorem lieDerivative_const (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (c : ℝ) :
    lieDerivative N_c i (fun _ : SUN_State_Concrete N_c => c) = 0 := by
  funext U; exact lieD'_const N_c i c U

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

/-- E(f+g) ≤ 2·E(f) + 2·E(g). PROVED via lieDerivReg_all + integral_mono. -/
theorem sunDirichletForm_subadditive {N_c : ℕ} [NeZero N_c]
    (f g : SUN_State_Concrete N_c → ℝ) :
    sunDirichletForm_concrete N_c (f + g) ≤
    2 * sunDirichletForm_concrete N_c f +
    2 * sunDirichletForm_concrete N_c g := by
  let μ := sunHaarProb N_c
  have hf  := lieDerivReg_all N_c f
  have hg  := lieDerivReg_all N_c g
  have hfg := lieDerivReg_all N_c (f + g)
  have hle : ∀ i : LieGenIndex N_c,
      ∫ U, (lieDerivative N_c i (f + g) U) ^ 2 ∂μ ≤
        2 * ∫ U, (lieDerivative N_c i f U) ^ 2 ∂μ +
        2 * ∫ U, (lieDerivative N_c i g U) ^ 2 ∂μ := by
    intro i
    -- (a+b)^2 ≤ 2a^2+2b^2: ring_nf first, then linarith
    have hpoint : ∀ U,
        (lieDerivative N_c i (f + g) U) ^ 2 ≤
        2 * (lieDerivative N_c i f U) ^ 2 +
        2 * (lieDerivative N_c i g U) ^ 2 := by
      intro U
      rw [lieDerivative_add N_c i f g]
      set a := lieDerivative N_c i f U
      set b := lieDerivative N_c i g U
      have h2ab : 2 * a * b ≤ a ^ 2 + b ^ 2 := two_mul_le_add_sq a b
      calc
        (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
        _ ≤ a ^ 2 + (a ^ 2 + b ^ 2) + b ^ 2 := by gcongr
        _ = 2 * a ^ 2 + 2 * b ^ 2 := by ring
    have hint1 : Integrable (fun U => 2 * (lieDerivative N_c i f U) ^ 2) μ :=
      (hf.sq_int i).const_mul 2
    have hint2 : Integrable (fun U => 2 * (lieDerivative N_c i g U) ^ 2) μ :=
      (hg.sq_int i).const_mul 2
    have h_int_le :
        ∫ U, (lieDerivative N_c i (f + g) U) ^ 2 ∂μ ≤
          ∫ U, (2 * (lieDerivative N_c i f U) ^ 2 +
                2 * (lieDerivative N_c i g U) ^ 2) ∂μ :=
      integral_mono (hfg.sq_int i) (hint1.add hint2) hpoint
    -- split integral via calc to avoid rw pattern matching issues
    have h_split :
        ∫ U, (2 * (lieDerivative N_c i f U) ^ 2 +
              2 * (lieDerivative N_c i g U) ^ 2) ∂μ =
          2 * ∫ U, (lieDerivative N_c i f U) ^ 2 ∂μ +
          2 * ∫ U, (lieDerivative N_c i g U) ^ 2 ∂μ :=
      calc ∫ U, (2 * (lieDerivative N_c i f U) ^ 2 +
              2 * (lieDerivative N_c i g U) ^ 2) ∂μ
            = ∫ U, (2 * (lieDerivative N_c i f U) ^ 2) ∂μ +
              ∫ U, (2 * (lieDerivative N_c i g U) ^ 2) ∂μ := by
                convert integral_add hint1 hint2 using 1
          _ = 2 * ∫ U, (lieDerivative N_c i f U) ^ 2 ∂μ +
              2 * ∫ U, (lieDerivative N_c i g U) ^ 2 ∂μ := by
                rw [integral_const_mul, integral_const_mul]
    exact h_int_le.trans (le_of_eq h_split)
  simp only [sunDirichletForm_concrete]
  calc ∑ i : LieGenIndex N_c, ∫ U, (lieDerivative N_c i (f + g) U) ^ 2 ∂μ
      ≤ ∑ i : LieGenIndex N_c,
            (2 * ∫ U, (lieDerivative N_c i f U) ^ 2 ∂μ +
             2 * ∫ U, (lieDerivative N_c i g U) ^ 2 ∂μ) :=
          Finset.sum_le_sum (fun i _ => hle i)
    _ = 2 * ∑ i : LieGenIndex N_c, ∫ U, (lieDerivative N_c i f U) ^ 2 ∂μ +
        2 * ∑ i : LieGenIndex N_c, ∫ U, (lieDerivative N_c i g U) ^ 2 ∂μ := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]


lemma sunDirichletForm_isDirichletForm {N_c : ℕ} [NeZero N_c] :
    IsDirichletForm (sunDirichletForm_concrete N_c) (sunHaarProb N_c) :=
  ⟨fun f => sunDirichletForm_nonneg f,
   fun f g => sunDirichletForm_subadditive f g⟩

/-- Strong Dirichlet form from an explicit normal-contraction input. -/
lemma sunDirichletForm_isDirichletFormStrong_of_contraction {N_c : ℕ} [NeZero N_c]
    (h_contraction : ∀ (f : SUN_State_Concrete N_c → ℝ) (n : ℝ), 0 < n →
      sunDirichletForm_concrete N_c (fun x => max (min (f x) n) (-n)) ≤
      sunDirichletForm_concrete N_c f) :
    IsDirichletFormStrong (sunDirichletForm_concrete N_c) (sunHaarProb N_c) :=
  ⟨sunDirichletForm_isDirichletForm,
   fun c f => sunDirichletForm_const_invariant f c,
   fun c f => sunDirichletForm_quadratic f c,
   fun f n hn => h_contraction f n hn⟩

#print axioms sunDirichletForm_isDirichletFormStrong_of_contraction

end
end YangMills
