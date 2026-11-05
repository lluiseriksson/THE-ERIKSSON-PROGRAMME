import YangMills.RG.PhysicalCycleFour

/-! Kernel coercivity through every actual fibre and coordinate.
First formal stage: longitudinal coordinate energy controls the full physical
norm for all actual cochains in the observation kernel, not only lifted fields.
The comparison with the full Hodge-plus-repair form is a separate obligation.
Candidate until own Colab build and dependency audit.
-/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
open MeanPenaltyCycleObstruction
noncomputable section
set_option maxHeartbeats 1800000
variable {d Nc : ℕ} [NeZero Nc]

abbrev ActualCycleFibreIndex (d Nc : ℕ) :=
  (Fin (d + 1) → ZMod 4) × (Fin (d + 2) × Fin (Nc^2 - 1))

noncomputable def actualCycleFibreProfile
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc) (z : ActualCycleFibreIndex d Nc) : Field :=
  fun t => A ((finBoxZModEquiv (d + 2) 4).symm (Fin.cases t z.1), z.2.1) z.2.2

private theorem actualCycleKernel_sum_zero
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc)
    (hA : actualCycleFullObservation cyclePairIntervals A = 0)
    (b : Fin 2) (z : ActualCycleFibreIndex d Nc) :
    (∑ t ∈ cyclePairIntervals b, actualCycleFibreProfile A z t) = 0 := by
  have hz := congrArg (fun v => v ((b, z.1), z.2)) hA
  change (∑ t ∈ cyclePairIntervals b, actualCycleFibreProfile A z t) /
    Real.sqrt ((cyclePairIntervals b).card : ℝ) = 0 at hz
  rw [(cyclePairIntervals_partition.1 b).2] at hz
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  exact (div_eq_zero_iff.mp hz).resolve_right hs

theorem actualCycleKernel_profile_pair_zero
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc)
    (hA : actualCycleFullObservation cyclePairIntervals A = 0)
    (z : ActualCycleFibreIndex d Nc) :
    actualCycleFibreProfile A z 0 + actualCycleFibreProfile A z 1 = 0 ∧
    actualCycleFibreProfile A z 2 + actualCycleFibreProfile A z 3 = 0 := by
  have h0 := actualCycleKernel_sum_zero A hA 0 z
  have h1 := actualCycleKernel_sum_zero A hA 1 z
  have h01 : (0 : ZMod 4) ≠ 1 := by decide
  have h23 : (2 : ZMod 4) ≠ 3 := by decide
  norm_num [cyclePairIntervals, Finset.sum_insert, Finset.sum_singleton,
    h01, h23] at h0 h1
  exact ⟨h0, h1⟩

theorem actualCycleKernel_fibre_coercive
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc)
    (hA : actualCycleFullObservation cyclePairIntervals A = 0)
    (z : ActualCycleFibreIndex d Nc) :
    (19 / 5 : ℝ) * normSq (actualCycleFibreProfile A z) ≤
      energy (actualCycleFibreProfile A z) := by
  rcases actualCycleKernel_profile_pair_zero A hA z with ⟨h01, h23⟩
  exact kernel_coercive _ h01 h23

private theorem actualCycleFibre_norm_sum (A : PhysicalGaugeOneCochain (d + 2) 4 Nc)
    (y : Fin (d + 1) → ZMod 4) (l : Fin (d + 2)) (k : Fin (Nc^2 - 1)) :
    (∑ t : ZMod 4, (A ((finBoxZModEquiv (d + 2) 4).symm
      (Fin.cases t y), l) k)^2) = normSq (actualCycleFibreProfile A (y, l, k)) := by
  change (∑ t : Fin 4, (actualCycleFibreProfile A (y, l, k) t)^2) = _
  simp [Fin.sum_univ_succ, normSq, add_assoc]

theorem actualCycleFibre_norm_decomposition
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc) :
    ‖A‖^2 = ∑ z : ActualCycleFibreIndex d Nc, normSq (actualCycleFibreProfile A z) := by
  classical
  have hn (p : PhysicalBond (d + 2) 4) : ‖A p‖^2 = ∑ k, (A p k)^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (A p)
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [hn]
  change (∑ p : FinBox (d + 2) 4 × Fin (d + 2), ∑ k, (A p k)^2) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : Fin (d + 2) → ZMod 4, ∑ l, ∑ k,
        (A ((finBoxZModEquiv (d + 2) 4).symm x, l) k)^2 := by
      exact (Equiv.sum_comp (finBoxZModEquiv (d + 2) 4).symm
        (fun x : FinBox (d + 2) 4 => ∑ l, ∑ k, (A (x, l) k)^2)).symm
    _ = ∑ z : ZMod 4 × (Fin (d + 1) → ZMod 4), ∑ l, ∑ k,
        (A ((finBoxZModEquiv (d + 2) 4).symm (Fin.cases z.1 z.2), l) k)^2 := by
      exact (Equiv.sum_comp (cycleCoordinateSplit (d := d) (n := 4)).symm
        (fun x : Fin (d + 2) → ZMod 4 => ∑ l, ∑ k,
          (A ((finBoxZModEquiv (d + 2) 4).symm x, l) k)^2)).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact actualCycleFibre_norm_sum A y l k

noncomputable def actualCycleLongitudinalEnergy
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc) : ℝ :=
  ∑ z : ActualCycleFibreIndex d Nc, energy (actualCycleFibreProfile A z)

theorem actualCycleKernel_coordinate_sum_coercive
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc)
    (hA : actualCycleFullObservation cyclePairIntervals A = 0) :
    (19 / 5 : ℝ) * (∑ z : ActualCycleFibreIndex d Nc,
      normSq (actualCycleFibreProfile A z)) ≤ actualCycleLongitudinalEnergy A := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun z _ => actualCycleKernel_fibre_coercive A hA z)

theorem actualCycleKernel_norm_coercive
    (A : PhysicalGaugeOneCochain (d + 2) 4 Nc)
    (hA : actualCycleFullObservation cyclePairIntervals A = 0) :
    (19 / 5 : ℝ) * ‖A‖^2 ≤ actualCycleLongitudinalEnergy A := by
  rw [actualCycleFibre_norm_decomposition]
  exact actualCycleKernel_coordinate_sum_coercive A hA

end
end YangMills.RG
