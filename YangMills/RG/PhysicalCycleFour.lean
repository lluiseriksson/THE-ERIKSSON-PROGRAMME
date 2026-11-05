import YangMills.RG.PhysicalCycleEnergy
import YangMills.RG.MeanPenaltyCycleObstruction

/-! Explicit four-cycle instance on actual physical divergence-zero cochains.
Candidate until own Colab compilation and dependency audit. This concerns a
fixed rectangular observation and fixed penalty, not all partitions or a gap.
-/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
open MeanPenaltyCycleObstruction
noncomputable section
set_option maxHeartbeats 1600000

abbrev cycleFourProfile (u : Field) : ZMod 4 → ℝ := u
abbrev cycleFourAlpha : ZMod 4 → ℝ := weight

def cyclePairIntervals (b : Fin 2) : Finset (ZMod 4) :=
  if b = 0 then {0, 1} else {2, 3}

theorem cyclePairIntervals_partition :
    (∀ b, (cyclePairIntervals b).Nonempty ∧ (cyclePairIntervals b).card = 2) ∧
    Disjoint (cyclePairIntervals 0) (cyclePairIntervals 1) ∧
    cyclePairIntervals 0 ∪ cyclePairIntervals 1 = Finset.univ := by
  decide

theorem cycleFour_scalar_identities (u : Field) :
    (∑ t : ZMod 4, cycleFourAlpha t *
      (cycleFourProfile u (t + 1) - cycleFourProfile u t)^2) = energy u ∧
    (∑ t : ZMod 4, (cycleFourProfile u t)^2) = normSq u ∧
    (∑ b : Fin 2, ((∑ t ∈ cyclePairIntervals b, cycleFourProfile u t) /
      Real.sqrt ((cyclePairIntervals b).card : ℝ))^2) = observedSq u := by
  have hs : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · change (∑ t : Fin 4, weight t * (u (t + 1) - u t)^2) = energy u
    have h1 : (1 : Fin 4) + 1 = 2 := by decide
    have h2 : (2 : Fin 4) + 1 = 3 := by decide
    have h3 : (3 : Fin 4) + 1 = 0 := by decide
    have hs3 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
    norm_num [Fin.sum_univ_succ, weight, energy, h1, h2, h3, hs3]
    <;> ring
  constructor
  · change (∑ t : Fin 4, (u t)^2) = normSq u
    simp [Fin.sum_univ_succ, normSq, add_assoc]
  · have h01 : (0 : ZMod 4) ≠ 1 := by decide
    have h23 : (2 : ZMod 4) ≠ 3 := by decide
    simp [Fin.sum_univ_succ, cyclePairIntervals, cycleFourProfile,
      Finset.sum_insert, Finset.sum_singleton, h01, h23, div_pow, hs, observedSq]
    <;> ring

variable {d Nc : ℕ} [NeZero Nc]

theorem physicalCycleFour_negative_defect (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) :
    inner ℝ (physicalCycleLift (d := d) hNc (cycleFourProfile witness))
      (flatGaugeHodgeK0CLM (d + 2) 4 Nc rho
        (physicalCycleLift hNc (cycleFourProfile witness))) +
    inner ℝ (physicalCycleLift (d := d) hNc (cycleFourProfile witness))
      (componentwiseWeightedRepairCLM (physicalCycleRepairWeights cycleFourAlpha)
        (physicalCycleLift hNc (cycleFourProfile witness))) +
    (19 / 5 : ℝ) * ‖actualCycleFullObservation cyclePairIntervals
      (physicalCycleLift (d := d) hNc (cycleFourProfile witness))‖^2 -
    (19 / 5 : ℝ) * ‖physicalCycleLift (d := d) hNc (cycleFourProfile witness)‖^2 =
      -(6 / 35 : ℝ) * (4 : ℝ)^(d + 1) := by
  rw [physicalCycleLift_total_energy, actualCycleFullObservation_lift_norm_sq,
    physicalCycleLift_norm_sq]
  rcases cycleFour_scalar_identities witness with ⟨he, hn, hc⟩
  rw [he, hn, hc]
  calc
    _ = (4 : ℝ)^(d + 1) * (energy witness + (19 / 5 : ℝ) * observedSq witness -
        (19 / 5 : ℝ) * normSq witness) := by ring
    _ = _ := by rw [witness_negative_defect]; ring

theorem physicalCycleFour_divergence_zero (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) 4 Nc)
      (physicalCycleLift hNc (cycleFourProfile witness)) = 0 :=
  physicalCycleLift_divergence_zero hNc rho (cycleFourProfile witness)

theorem physicalCycleFour_fixed_penalty_false (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) :
    ¬ (∀ A : PhysicalGaugeOneCochain (d + 2) 4 Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) 4 Nc) A = 0 →
      (19 / 5 : ℝ) * ‖A‖^2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM (d + 2) 4 Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM
          (physicalCycleRepairWeights cycleFourAlpha) A) +
        (19 / 5 : ℝ) * ‖actualCycleFullObservation cyclePairIntervals A‖^2) := by
  intro h
  have hi := h (physicalCycleLift hNc (cycleFourProfile witness))
    (physicalCycleFour_divergence_zero hNc rho)
  have hd := physicalCycleFour_negative_defect (d := d) hNc rho
  have hp : 0 < (4 : ℝ)^(d + 1) := pow_pos (by norm_num) _
  nlinarith

end
end YangMills.RG
