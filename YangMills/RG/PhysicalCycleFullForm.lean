import YangMills.RG.PhysicalCycleKernel

/-! Actual full-form kernel coercivity and fixed-penalty counterexample.
All transport identities and inequalities are derived for actual cochains.
Candidate until own Colab compilation, oracle and final paired reproduction.
No all-partitions, free-penalty, interacting or continuum conclusion.
-/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
open MeanPenaltyCycleObstruction
noncomputable section
set_option maxHeartbeats 2000000
variable {d Nc : ℕ} [NeZero Nc]

noncomputable def physicalCycleFourForm (rho : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc) : ℝ :=
  inner ℝ A (flatGaugeHodgeK0CLM (d + 2) 4 Nc rho A) +
    inner ℝ A (componentwiseWeightedRepairCLM
      (physicalCycleRepairWeights cycleFourAlpha) A)

private theorem cycleFibre_shift_zero (t : ZMod 4) (y : Fin (d + 1) → ZMod 4) :
    ((finBoxZModEquiv (d + 2) 4).symm (Fin.cases t y)).shift 0 =
      (finBoxZModEquiv (d + 2) 4).symm (Fin.cases (t + 1) y) := by
  apply (finBoxZModEquiv (d + 2) 4).injective
  rw [finBoxZModEquiv_shift]
  simp only [Equiv.apply_symm_apply]
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [Pi.add_apply, Pi.single_apply]

theorem actualCycleLongitudinalEnergy_eq_directional
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc) :
    actualCycleLongitudinalEnergy A =
      ∑ x : FinBox (d + 2) 4, ∑ l : Fin (d + 2),
        cycleFourAlpha (finBoxZModEquiv (d + 2) 4 x 0) *
          ‖A (x.shift 0, l) - A (x, l)‖^2 := by
  classical
  symm
  have hn (x : FinBox (d + 2) 4) (l : Fin (d + 2)) :
      ‖A (x.shift 0, l) - A (x, l)‖^2 =
        ∑ k, (A (x.shift 0, l) k - A (x, l) k)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  have hf (z : ActualCycleFibreIndex d Nc) :
      (∑ t : ZMod 4, cycleFourAlpha t *
        (actualCycleFibreProfile A z (t + (1 : ZMod 4)) - actualCycleFibreProfile A z t)^2) =
      energy (actualCycleFibreProfile A z) :=
    (cycleFour_scalar_identities (actualCycleFibreProfile A z)).1
  simp_rw [hn, Finset.mul_sum]
  calc
    _ = ∑ x : Fin (d + 2) → ZMod 4, ∑ l, ∑ k, cycleFourAlpha (x 0) *
        (A (((finBoxZModEquiv (d + 2) 4).symm x).shift 0, l) k -
          A ((finBoxZModEquiv (d + 2) 4).symm x, l) k)^2 := by
      simpa only [Equiv.apply_symm_apply] using
        (Equiv.sum_comp (finBoxZModEquiv (d + 2) 4).symm
          (fun x : FinBox (d + 2) 4 => ∑ l, ∑ k,
            cycleFourAlpha (finBoxZModEquiv (d + 2) 4 x 0) *
              (A (x.shift 0, l) k - A (x, l) k)^2)).symm
    _ = ∑ z : ZMod 4 × (Fin (d + 1) → ZMod 4), ∑ l, ∑ k,
        cycleFourAlpha z.1 *
          (A (((finBoxZModEquiv (d + 2) 4).symm (Fin.cases z.1 z.2)).shift 0, l) k -
            A ((finBoxZModEquiv (d + 2) 4).symm (Fin.cases z.1 z.2), l) k)^2 := by
      exact (Equiv.sum_comp (cycleCoordinateSplit (d := d) (n := 4)).symm
        (fun x : Fin (d + 2) → ZMod 4 => ∑ l, ∑ k, cycleFourAlpha (x 0) *
          (A (((finBoxZModEquiv (d + 2) 4).symm x).shift 0, l) k -
            A ((finBoxZModEquiv (d + 2) 4).symm x, l) k)^2)).symm
    _ = _ := by
      simp_rw [cycleFibre_shift_zero]
      simp only [actualCycleLongitudinalEnergy, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact hf (y, l, k)

theorem physicalCycleFour_total_energy_sum (rho : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc) :
    physicalCycleFourForm rho A =
      ∑ p : PhysicalGradientIndex (d + 2) 4,
        cycleFourAlpha (finBoxZModEquiv (d + 2) 4 p.2.1 0) *
          ‖A ((p.2.1).shift p.1, p.2.2) - A p.2‖^2 := by
  unfold physicalCycleFourForm
  rw [← componentwiseFlatGradient_eq_hodge rho,
    componentwiseFlatGradient_energy, componentwiseWeightedRepair_energy,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  dsimp [physicalCycleRepairWeights]
  ring

theorem actualCycleLongitudinalEnergy_le_total (rho : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc) :
    actualCycleLongitudinalEnergy A ≤ physicalCycleFourForm rho A := by
  classical
  rw [actualCycleLongitudinalEnergy_eq_directional, physicalCycleFour_total_energy_sum]
  simp only [PhysicalGradientIndex, Fintype.sum_prod_type]
  have ha (t : ZMod 4) : 0 ≤ cycleFourAlpha t :=
    le_trans (by norm_num) (weights_admissible.2 t).1
  let F : Fin (d + 2) → ℝ := fun i =>
    ∑ x : FinBox (d + 2) 4, ∑ l : Fin (d + 2),
      cycleFourAlpha (finBoxZModEquiv (d + 2) 4 x 0) *
        ‖A (x.shift i, l) - A (x, l)‖^2
  have hF (i : Fin (d + 2)) : 0 ≤ F i := by
    exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun l _ =>
      mul_nonneg (ha _) (sq_nonneg _)))
  change F 0 ≤ ∑ i, F i
  exact Finset.single_le_sum (fun i _ => hF i) (Finset.mem_univ (0 : Fin (d + 2)))

theorem physicalCycleFour_kernel_coercive (rho : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc)
    (hA : actualCycleFullObservation cyclePairIntervals A = 0) :
    (19 / 5 : ℝ) * ‖A‖^2 ≤ physicalCycleFourForm rho A :=
  le_trans (actualCycleKernel_norm_coercive A hA) (actualCycleLongitudinalEnergy_le_total rho A)

theorem physicalCycleFour_kernel_fixed_penalty_counterexample
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) :
    (∀ A : PhysicalGaugeOneCochain (d + 2) 4 Nc,
      actualCycleFullObservation cyclePairIntervals A = 0 →
      (19 / 5 : ℝ) * ‖A‖^2 ≤ physicalCycleFourForm rho A) ∧
    ¬ (∀ A : PhysicalGaugeOneCochain (d + 2) 4 Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) 4 Nc) A = 0 →
      (19 / 5 : ℝ) * ‖A‖^2 ≤ physicalCycleFourForm rho A +
        (19 / 5 : ℝ) * ‖actualCycleFullObservation cyclePairIntervals A‖^2) := by
  constructor
  · intro A hA
    exact physicalCycleFour_kernel_coercive rho A hA
  · exact physicalCycleFour_fixed_penalty_false hNc rho

end
end YangMills.RG
