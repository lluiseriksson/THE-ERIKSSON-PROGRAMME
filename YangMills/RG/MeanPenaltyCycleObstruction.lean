import Mathlib

/-!
Exact four-cycle preservation of the fixed-penalty counterexample.
Finite real fields only: no physical-lattice embedding or general rectangular
partition theorem is claimed. The weights and the witness are constructed.
Candidate until own Colab compilation and axiom-oracle validation.
-/

namespace YangMills.RG.MeanPenaltyCycleObstruction

abbrev Field := Fin 4 → ℝ

def weight : Fin 4 → ℝ := ![1, 6, 4, 1]

def energy (u : Field) : ℝ :=
  (u 1 - u 0)^2 + 6 * (u 2 - u 1)^2 +
    4 * (u 3 - u 2)^2 + (u 0 - u 3)^2

def normSq (u : Field) : ℝ :=
  (u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2

/-- Squared Euclidean norm of the two normalized block means. -/
def observedSq (u : Field) : ℝ :=
  ((u 0 + u 1)^2 + (u 2 + u 3)^2) / 2

def observation (u : Field) : Fin 2 → ℝ :=
  ![(u 0 + u 1) / Real.sqrt 2, (u 2 + u 3) / Real.sqrt 2]

def meanProjection (u : Field) : Field :=
  ![(u 0 + u 1) / 2, (u 0 + u 1) / 2,
    (u 2 + u 3) / 2, (u 2 + u 3) / 2]

def witness : Field := ![19 / 14, -9 / 14, -5 / 14, -5 / 14]

theorem weights_admissible :
    (weight 0 + weight 1 + weight 2 + weight 3) / 4 = 3 ∧
      ∀ i, 1 ≤ weight i ∧ weight i ≤ 2 * 3 := by
  constructor
  · norm_num [weight]
  · intro i
    fin_cases i <;> norm_num [weight]

theorem energy_from_actual_weights (u : Field) :
    energy u = weight 0 * (u 1 - u 0)^2 + weight 1 * (u 2 - u 1)^2 +
      weight 2 * (u 3 - u 2)^2 + weight 3 * (u 0 - u 3)^2 := by
  norm_num [energy, weight]

theorem observedSq_eq_output (u : Field) :
    observedSq u = (observation u 0)^2 + (observation u 1)^2 := by
  have hs : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [observedSq, observation]
  simp only [div_pow, hs]
  ring

theorem normalized_mean_norm (u : Field) :
    normSq (meanProjection u) = observedSq u := by
  dsimp [normSq, meanProjection, observedSq]
  ring

theorem orthogonal_mean_decomposition (u : Field) :
    normSq u = normSq (fun i => u i - meanProjection u i) + observedSq u := by
  dsimp [normSq, meanProjection, observedSq]
  ring

theorem kernel_square_identity (u : Field)
    (h01 : u 0 + u 1 = 0) (h23 : u 2 + u 3 = 0) :
    energy u - (19 / 5 : ℝ) * normSq u =
      (17 / 5 : ℝ) * (u 0 + (35 / 17 : ℝ) * u 2)^2 +
        (84 / 85 : ℝ) * (u 2)^2 := by
  have h1 : u 1 = -u 0 := by linarith
  have h3 : u 3 = -u 2 := by linarith
  simp only [energy, normSq, h1, h3]
  ring

theorem kernel_coercive (u : Field)
    (h01 : u 0 + u 1 = 0) (h23 : u 2 + u 3 = 0) :
    (19 / 5 : ℝ) * normSq u ≤ energy u := by
  have hid := kernel_square_identity u h01 h23
  nlinarith [sq_nonneg (u 0 + (35 / 17 : ℝ) * u 2), sq_nonneg (u 2)]

theorem witness_exact_values :
    energy witness = 52 / 7 ∧ normSq witness = 123 / 49 ∧
      observedSq witness = 25 / 49 := by
  norm_num [energy, normSq, observedSq, witness]

theorem witness_negative_defect :
    energy witness + (19 / 5 : ℝ) * observedSq witness -
      (19 / 5 : ℝ) * normSq witness = -6 / 35 := by
  norm_num [energy, normSq, observedSq, witness]

theorem fixed_penalty_coercivity_false :
    ¬ (∀ u : Field, (19 / 5 : ℝ) * normSq u ≤
      energy u + (19 / 5 : ℝ) * observedSq u) := by
  intro h
  have hw := h witness
  have hd := witness_negative_defect
  linarith

end YangMills.RG.MeanPenaltyCycleObstruction
