import YangMills.RG.NearLogAnalytic

open Asymptotics

#check HasFPowerSeriesAt.isBigO_sub_partialSum_pow
#check HasFPowerSeriesAt.hasDerivAt
#check HasFPowerSeriesAt.coeff_zero
#check FormalMultilinearSeries.partialSum

theorem test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) (hf : AnalyticAt ℝ f 0) :
    (fun t : ℝ => f t - f 0 - t • deriv f 0) =O[nhds 0]
      (fun t : ℝ => t ^ 2) := by
  rcases hf with ⟨p, hp⟩
  have h := hp.isBigO_sub_partialSum_pow 2
  have hp0 : p 0 (fun _ => (0 : ℝ)) = f 0 := hp.coeff_zero _
  have hp1 : p 1 (fun _ => (1 : ℝ)) = deriv f 0 := hp.hasDerivAt.deriv.symm
  refine h.congr' ?_ (Filter.Eventually.of_forall fun t => by
    simp [Real.norm_eq_abs, sq_abs])
  filter_upwards [] with t
  simp only [zero_add]
  rw [FormalMultilinearSeries.partialSum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
  have hp0t : p 0 (fun _ : Fin 0 => t) = f 0 := hp.coeff_zero _
  rw [hp0t, zero_add]
  have hlin : p 1 (fun _ : Fin 1 => t) = t • deriv f 0 := by
    have hmap := (p 1).map_smul_univ
      (fun _ : Fin 1 => t) (fun _ : Fin 1 => (1 : ℝ))
    simpa [hp1] using hmap
  rw [hlin]
  abel
