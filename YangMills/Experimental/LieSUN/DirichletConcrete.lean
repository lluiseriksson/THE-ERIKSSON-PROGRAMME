import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.Experimental.LieSUN.LieExpCurve
import YangMills.Experimental.LieSUN.LieDerivativeBridge

open scoped Matrix
open MeasureTheory YangMills

/-!
# DirichletConcrete — Spike v3

Same as v2 but use sunHaarProb (already IsProbabilityMeasure) instead of
raw Measure.haar which needs TopologicalGroup instances not yet in P8.

Tests:
1. lieDeriv_const ✅ (unconditional)
2. lieDeriv_add under IsDiffAlong
3. lieDeriv_smul under IsDiffAlong
4. dirichletForm_subadditive (the key test)
-/

-- Generator axioms (2 IN)
axiom generatorMatrix' (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    Matrix (Fin N_c) (Fin N_c) ℂ

axiom gen_skewHerm (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix' N_c i)ᴴ = -(generatorMatrix' N_c i)

axiom gen_trace_zero (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix' N_c i).trace = 0

-- Concrete Lie derivative
noncomputable def lieDeriv (N_c : ℕ) [NeZero N_c]
    (i : Fin (N_c ^ 2 - 1))
    (f : SUN_State_Concrete N_c → ℝ)
    (U : SUN_State_Concrete N_c) : ℝ :=
  lieDerivExp
    (generatorMatrix' N_c i) (gen_skewHerm N_c i) (gen_trace_zero N_c i) f U

-- TEST 1: const — unconditional ✅
theorem lieDeriv_const (N_c : ℕ) [NeZero N_c]
    (i : Fin (N_c ^ 2 - 1)) (c : ℝ) (U : SUN_State_Concrete N_c) :
    lieDeriv N_c i (fun _ => c) U = 0 := by
  simp [lieDeriv, lieDerivExp_const]

-- Regularity predicate
def IsDiffAlong (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1))
    (f : SUN_State_Concrete N_c → ℝ) : Prop :=
  ∀ U : SUN_State_Concrete N_c,
    DifferentiableAt ℝ (fun t => f (lieExpCurve N_c
      (generatorMatrix' N_c i) (gen_skewHerm N_c i) (gen_trace_zero N_c i) U t)) 0

-- TEST 2: add under IsDiffAlong
theorem lieDeriv_add (N_c : ℕ) [NeZero N_c]
    (i : Fin (N_c ^ 2 - 1)) (f g : SUN_State_Concrete N_c → ℝ)
    (hf : IsDiffAlong N_c i f) (hg : IsDiffAlong N_c i g)
    (U : SUN_State_Concrete N_c) :
    lieDeriv N_c i (fun x => f x + g x) U = lieDeriv N_c i f U + lieDeriv N_c i g U := by
  simp only [lieDeriv]
  exact lieDerivExp_add (X := generatorMatrix' N_c i) (hX := gen_skewHerm N_c i)
    (htr := gen_trace_zero N_c i) (f := f) (g := g) (U := U) (hf U) (hg U)

-- TEST 3: smul under IsDiffAlong
theorem lieDeriv_smul (N_c : ℕ) [NeZero N_c]
    (i : Fin (N_c ^ 2 - 1)) (c : ℝ) (f : SUN_State_Concrete N_c → ℝ)
    (hf : IsDiffAlong N_c i f) (U : SUN_State_Concrete N_c) :
    lieDeriv N_c i (fun x => c * f x) U = c * lieDeriv N_c i f U := by
  simp only [lieDeriv]
  exact lieDerivExp_smul (X := generatorMatrix' N_c i) (hX := gen_skewHerm N_c i)
    (htr := gen_trace_zero N_c i) (c := c) (f := f) (U := U) (hf U)

private lemma sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 :=
  by nlinarith [sq_nonneg (a - b)]

-- Use sunHaarProb which is already IsProbabilityMeasure (no TopologicalGroup needed)
noncomputable def dirichletForm' (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : ℝ :=
  ∑ i : Fin (N_c ^ 2 - 1),
    ∫ U, (lieDeriv N_c i f U) ^ 2 ∂(sunHaarProb N_c)

-- TEST 4: subadditivity ← THE KEY TEST
-- hfg2 is an explicit hypothesis (measurability of lieDeriv not yet auto-provable)
theorem dirichletForm_subadditive (N_c : ℕ) [NeZero N_c]
    (f g : SUN_State_Concrete N_c → ℝ)
    (hf : ∀ i, IsDiffAlong N_c i f) (hg : ∀ i, IsDiffAlong N_c i g)
    (hf2 : ∀ i, Integrable (fun U => (lieDeriv N_c i f U) ^ 2) (sunHaarProb N_c))
    (hg2 : ∀ i, Integrable (fun U => (lieDeriv N_c i g U) ^ 2) (sunHaarProb N_c))
    (hfg2 : ∀ i, Integrable
        (fun U => (lieDeriv N_c i (fun x => f x + g x) U) ^ 2) (sunHaarProb N_c)) :
    dirichletForm' N_c (fun x => f x + g x) ≤
    2 * dirichletForm' N_c f + 2 * dirichletForm' N_c g := by
  -- Prove per-index bound first, then sum
  have hle : ∀ i : Fin (N_c ^ 2 - 1),
      ∫ U, (lieDeriv N_c i (fun x => f x + g x) U) ^ 2 ∂(sunHaarProb N_c) ≤
      2 * ∫ U, (lieDeriv N_c i f U) ^ 2 ∂(sunHaarProb N_c) +
      2 * ∫ U, (lieDeriv N_c i g U) ^ 2 ∂(sunHaarProb N_c) := by
    intro i
    have hadd := lieDeriv_add N_c i f g (hf i) (hg i)
    -- hfg2 i comes from explicit hypothesis
    have hpoint : ∀ U,
        (lieDeriv N_c i (fun x => f x + g x) U) ^ 2 ≤
        2 * (lieDeriv N_c i f U) ^ 2 + 2 * (lieDeriv N_c i g U) ^ 2 := by
      intro U; rw [hadd U]
      nlinarith [sq_nonneg (lieDeriv N_c i f U - lieDeriv N_c i g U)]
    have hRhsInt : Integrable
        (fun U => 2 * (lieDeriv N_c i f U) ^ 2 + 2 * (lieDeriv N_c i g U) ^ 2)
        (sunHaarProb N_c) :=
      ((hf2 i).const_mul 2).add ((hg2 i).const_mul 2)
    calc ∫ U, (lieDeriv N_c i (fun x => f x + g x) U) ^ 2 ∂(sunHaarProb N_c)
        ≤ ∫ U, (2 * (lieDeriv N_c i f U) ^ 2 + 2 * (lieDeriv N_c i g U) ^ 2)
              ∂(sunHaarProb N_c) :=
            integral_mono (hfg2 i) hRhsInt (fun U => hpoint U)
      _ = 2 * ∫ U, (lieDeriv N_c i f U) ^ 2 ∂(sunHaarProb N_c) +
          2 * ∫ U, (lieDeriv N_c i g U) ^ 2 ∂(sunHaarProb N_c) := by
            rw [integral_add ((hf2 i).const_mul 2) ((hg2 i).const_mul 2),
                integral_const_mul, integral_const_mul]
  -- Sum over all generators
  simp only [dirichletForm']
  calc ∑ i, ∫ U, (lieDeriv N_c i (fun x => f x + g x) U) ^ 2 ∂(sunHaarProb N_c)
      ≤ ∑ i, (2 * ∫ U, (lieDeriv N_c i f U) ^ 2 ∂(sunHaarProb N_c) +
              2 * ∫ U, (lieDeriv N_c i g U) ^ 2 ∂(sunHaarProb N_c)) :=
          Finset.sum_le_sum (fun i _ => hle i)
    _ = 2 * ∑ i, ∫ U, (lieDeriv N_c i f U) ^ 2 ∂(sunHaarProb N_c) +
        2 * ∑ i, ∫ U, (lieDeriv N_c i g U) ^ 2 ∂(sunHaarProb N_c) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
