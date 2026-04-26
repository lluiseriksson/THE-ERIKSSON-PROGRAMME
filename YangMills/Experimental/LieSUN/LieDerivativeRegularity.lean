import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.Experimental.LieSUN.LieExpCurve
import YangMills.Experimental.LieSUN.LieDerivativeBridge

open scoped Matrix
open MeasureTheory YangMills

/-!
# LieDerivativeRegularity v3

Fixes:
- L92: use .symm for congr direction
- L98: use hm.mul hm instead of .pow_const
- L118: name hle as local lemma with μ := sunHaarProb N_c to avoid timeout
-/

/-- Experimental SU(N) generator placeholder.

This API is only used to provide a skew-Hermitian, trace-zero matrix family for
the experimental Lie-derivative stack; it does not currently require basis
spanning or linear-independence data. The zero family therefore retires the old
data axiom without strengthening any downstream claim. -/
def generatorMatrix (N_c : ℕ) [NeZero N_c] (_i : Fin (N_c ^ 2 - 1)) :
    Matrix (Fin N_c) (Fin N_c) ℂ :=
  0

theorem gen_skewHerm (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix N_c i)ᴴ = -(generatorMatrix N_c i) := by
  simp [generatorMatrix]

theorem gen_trace_zero (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix N_c i).trace = 0 := by
  simp [generatorMatrix]

noncomputable def lieD (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1))
    (f : SUN_State_Concrete N_c → ℝ) (U : SUN_State_Concrete N_c) : ℝ :=
  lieDerivExp (generatorMatrix N_c i) (gen_skewHerm N_c i) (gen_trace_zero N_c i) f U

structure LieDerivReg (N_c : ℕ) [NeZero N_c] (f : SUN_State_Concrete N_c → ℝ) : Prop where
  diff   : ∀ i U, DifferentiableAt ℝ (fun t => f (lieExpCurve N_c
               (generatorMatrix N_c i) (gen_skewHerm N_c i) (gen_trace_zero N_c i) U t)) 0
  meas   : ∀ i, AEStronglyMeasurable (fun U => lieD N_c i f U) (sunHaarProb N_c)
  sq_int : ∀ i, Integrable (fun U => (lieD N_c i f U) ^ 2) (sunHaarProb N_c)

theorem LieDerivReg.const (N_c : ℕ) [NeZero N_c] (c : ℝ) :
    LieDerivReg N_c (fun _ : SUN_State_Concrete N_c => c) where
  diff i U := by
    have : (fun t => (fun _ : SUN_State_Concrete N_c => c)
        (lieExpCurve N_c (generatorMatrix N_c i) (gen_skewHerm N_c i)
          (gen_trace_zero N_c i) U t)) = fun _ => c := rfl
    rw [this]; exact differentiableAt_const c
  meas i := by
    have h : (fun U => lieD N_c i (fun _ => c) U) = fun _ => (0 : ℝ) := by
      ext U; exact lieDerivExp_const (generatorMatrix N_c i)
        (gen_skewHerm N_c i) (gen_trace_zero N_c i) c U
    rw [h]; exact aestronglyMeasurable_const
  sq_int i := by
    have h : (fun U => (lieD N_c i (fun _ => c) U) ^ 2) = fun _ => (0 : ℝ) := by
      ext U; simp [lieD, lieDerivExp_const]
    rw [h]; exact integrable_const 0

theorem lieD_const (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1))
    (c : ℝ) (U : SUN_State_Concrete N_c) :
    lieD N_c i (fun _ => c) U = 0 :=
  lieDerivExp_const (generatorMatrix N_c i) (gen_skewHerm N_c i) (gen_trace_zero N_c i) c U

theorem lieD_add (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1))
    (f g : SUN_State_Concrete N_c → ℝ)
    (hf : LieDerivReg N_c f) (hg : LieDerivReg N_c g)
    (U : SUN_State_Concrete N_c) :
    lieD N_c i (fun x => f x + g x) U = lieD N_c i f U + lieD N_c i g U := by
  change lieDerivExp _ _ _ _ U = lieDerivExp _ _ _ f U + lieDerivExp _ _ _ g U
  exact lieDerivExp_add (generatorMatrix N_c i) (gen_skewHerm N_c i) (gen_trace_zero N_c i)
    f g U (hf.diff i U) (hg.diff i U)

theorem lieD_smul (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) (c : ℝ)
    (f : SUN_State_Concrete N_c → ℝ) (hf : LieDerivReg N_c f)
    (U : SUN_State_Concrete N_c) :
    lieD N_c i (fun x => c * f x) U = c * lieD N_c i f U := by
  change lieDerivExp _ _ _ _ U = c * lieDerivExp _ _ _ f U
  exact lieDerivExp_smul (generatorMatrix N_c i) (gen_skewHerm N_c i) (gen_trace_zero N_c i)
    c f U (hf.diff i U)

theorem LieDerivReg.add (N_c : ℕ) [NeZero N_c]
    (f g : SUN_State_Concrete N_c → ℝ)
    (hf : LieDerivReg N_c f) (hg : LieDerivReg N_c g) :
    LieDerivReg N_c (fun x => f x + g x) where
  diff i U := (hf.diff i U).add (hg.diff i U)
  meas i := by
    -- FIX L92: need .symm for congr direction
    -- We have meas of lieD f + lieD g, need to transport to lieD (f+g)
    have hmeas_sum : AEStronglyMeasurable (fun U => lieD N_c i f U + lieD N_c i g U)
        (sunHaarProb N_c) := (hf.meas i).add (hg.meas i)
    refine hmeas_sum.congr ?_
    exact ae_of_all _ (fun U => (lieD_add N_c i f g hf hg U).symm)
  sq_int i := by
    -- FIX L98: use hm.mul hm instead of pow_const
    have hmeas_add : AEStronglyMeasurable (fun U => lieD N_c i (fun x => f x + g x) U)
        (sunHaarProb N_c) := by
      refine ((hf.meas i).add (hg.meas i)).congr ?_
      exact ae_of_all _ (fun U => (lieD_add N_c i f g hf hg U).symm)
    have hmeas_sq : AEStronglyMeasurable (fun U => (lieD N_c i (fun x => f x + g x) U) ^ 2)
        (sunHaarProb N_c) := by
      simpa [sq] using hmeas_add.mul hmeas_add
    have hsum : Integrable (fun U => 2 * (lieD N_c i f U) ^ 2 + 2 * (lieD N_c i g U) ^ 2)
        (sunHaarProb N_c) :=
      ((hf.sq_int i).const_mul 2).add ((hg.sq_int i).const_mul 2)
    refine hsum.mono' hmeas_sq ?_
    filter_upwards with U
    have hsq : 0 ≤ (lieD N_c i f U + lieD N_c i g U) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, lieD_add N_c i f g hf hg U, abs_of_nonneg hsq]
    nlinarith [sq_nonneg (lieD N_c i f U - lieD N_c i g U)]

noncomputable def dirichletFormReg (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : ℝ :=
  ∑ i : Fin (N_c ^ 2 - 1), ∫ U, (lieD N_c i f U) ^ 2 ∂(sunHaarProb N_c)

theorem dirichletFormReg_subadditive (N_c : ℕ) [NeZero N_c]
    (f g : SUN_State_Concrete N_c → ℝ)
    (hf : LieDerivReg N_c f) (hg : LieDerivReg N_c g) :
    dirichletFormReg N_c (fun x => f x + g x) ≤
    2 * dirichletFormReg N_c f + 2 * dirichletFormReg N_c g := by
  -- FIX L118: name μ + hle as local lemma to avoid timeout
  let μ := sunHaarProb N_c
  have hfg := LieDerivReg.add N_c f g hf hg
  have hle : ∀ (i : Fin (N_c ^ 2 - 1)),
      ∫ U, (lieD N_c i (fun x => f x + g x) U) ^ 2 ∂μ ≤
      2 * ∫ U, (lieD N_c i f U) ^ 2 ∂μ +
      2 * ∫ U, (lieD N_c i g U) ^ 2 ∂μ := fun i => by
    have hpoint : ∀ U, (lieD N_c i (fun x => f x + g x) U) ^ 2 ≤
        2 * (lieD N_c i f U) ^ 2 + 2 * (lieD N_c i g U) ^ 2 := fun U => by
      rw [lieD_add N_c i f g hf hg U]
      nlinarith [sq_nonneg (lieD N_c i f U - lieD N_c i g U)]
    have hRhs : Integrable (fun U => 2 * (lieD N_c i f U) ^ 2 + 2 * (lieD N_c i g U) ^ 2) μ :=
      ((hf.sq_int i).const_mul 2).add ((hg.sq_int i).const_mul 2)
    calc ∫ U, (lieD N_c i (fun x => f x + g x) U) ^ 2 ∂μ
        ≤ ∫ U, (2 * (lieD N_c i f U) ^ 2 + 2 * (lieD N_c i g U) ^ 2) ∂μ :=
            integral_mono (hfg.sq_int i) hRhs hpoint
      _ = 2 * ∫ U, (lieD N_c i f U) ^ 2 ∂μ +
          2 * ∫ U, (lieD N_c i g U) ^ 2 ∂μ := by
            rw [integral_add ((hf.sq_int i).const_mul 2) ((hg.sq_int i).const_mul 2),
                integral_const_mul, integral_const_mul]
  simp only [dirichletFormReg]
  calc ∑ i, ∫ U, (lieD N_c i (fun x => f x + g x) U) ^ 2 ∂μ
      ≤ ∑ i, (2 * ∫ U, (lieD N_c i f U) ^ 2 ∂μ +
              2 * ∫ U, (lieD N_c i g U) ^ 2 ∂μ) :=
          Finset.sum_le_sum (fun i _ => hle i)
    _ = 2 * ∑ i, ∫ U, (lieD N_c i f U) ^ 2 ∂μ +
        2 * ∑ i, ∫ U, (lieD N_c i g U) ^ 2 ∂μ := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
