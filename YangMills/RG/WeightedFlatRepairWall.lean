import YangMills.RG.UniformPhysicalCoarseRankWall

/-! Concrete local weighted curl/divergence repairs. No rank bound is imposed
on the repair. These are finite unit-spacing flat operators, not a supplied
Wilson Hessian or a continuum theorem. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace

section Weight
variable {α V : Type*} [Fintype α]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

noncomputable def coordinateWeightCLM (w : α → ℝ) :
    PiLp 2 (fun _ : α => V) →L[ℝ] PiLp 2 (fun _ : α => V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => w i • x i)
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        change w i • (x i + y i) = w i • x i + w i • y i
        exact smul_add _ _ _
      map_smul' := by
        intro r x
        apply PiLp.ext
        intro i
        change w i • (r • x i) = r • (w i • x i)
        simp only [smul_smul, mul_comm] }

theorem coordinateWeight_inner (w : α → ℝ) (x : PiLp 2 (fun _ : α => V)) :
    inner ℝ x (coordinateWeightCLM w x) = ∑ i, w i * ‖x i‖ ^ 2 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change inner ℝ (x i) (w i • x i) = _
  rw [inner_smul_right, real_inner_self_eq_norm_sq]

theorem coordinateWeight_inner_le (w : α → ℝ) (M : ℝ) (hw : ∀ i, w i ≤ M)
    (x : PiLp 2 (fun _ : α => V)) :
    inner ℝ x (coordinateWeightCLM w x) ≤ M * ‖x‖ ^ 2 := by
  classical
  rw [coordinateWeight_inner, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _))

theorem coordinateWeight_inner_nonneg (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : PiLp 2 (fun _ : α => V)) : 0 ≤ inner ℝ x (coordinateWeightCLM w x) := by
  classical
  rw [coordinateWeight_inner]
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i) (sq_nonneg _))

@[simp] theorem coordinateWeight_one_apply (x : PiLp 2 (fun _ : α => V)) :
    coordinateWeightCLM (fun _ : α => (1 : ℝ)) x = x := by
  apply PiLp.ext
  intro i
  change (1 : ℝ) • x i = x i
  exact one_smul ℝ (x i)
end Weight

section Physical
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

noncomputable def weightedFlatRepairCLM (ρ : SUNAdjointModel Nc)
    (w : PhysicalPlaquette d n → ℝ) (v : FinBox d n → ℝ) :
    PhysicalGaugeOneCochain d n Nc →L[ℝ] PhysicalGaugeOneCochain d n Nc :=
  let D := covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc)
  let Q := gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d n Nc)
  D.adjoint.comp ((coordinateWeightCLM w).comp D) +
    Q.adjoint.comp ((coordinateWeightCLM v).comp Q)

theorem weightedFlatRepair_inner (ρ : SUNAdjointModel Nc)
    (w : PhysicalPlaquette d n → ℝ) (v : FinBox d n → ℝ)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (weightedFlatRepairCLM ρ w v A) =
      inner ℝ (covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc) A)
        (coordinateWeightCLM w (covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc) A)) +
      inner ℝ (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d n Nc) A)
        (coordinateWeightCLM v (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d n Nc) A)) := by
  simp only [weightedFlatRepairCLM, ContinuousLinearMap.add_apply, inner_add_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem weightedFlatRepair_nonneg (ρ : SUNAdjointModel Nc)
    (w : PhysicalPlaquette d n → ℝ) (v : FinBox d n → ℝ)
    (hw : ∀ p, 0 ≤ w p) (hv : ∀ x, 0 ≤ v x) (A : PhysicalGaugeOneCochain d n Nc) :
    0 ≤ inner ℝ A (weightedFlatRepairCLM ρ w v A) := by
  rw [weightedFlatRepair_inner]
  exact add_nonneg (coordinateWeight_inner_nonneg w hw _) (coordinateWeight_inner_nonneg v hv _)

theorem weightedFlatRepair_unit_energy (ρ : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (weightedFlatRepairCLM ρ (fun _ => 1) (fun _ => 1) A) =
      inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) := by
  rw [weightedFlatRepair_inner, coordinateWeight_one_apply, coordinateWeight_one_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  exact (flatGaugeHodgeK0_inner_right ρ A).symm

theorem weightedFlatRepair_le_flat (ρ : SUNAdjointModel Nc)
    (w : PhysicalPlaquette d n → ℝ) (v : FinBox d n → ℝ) (M : ℝ)
    (hw : ∀ p, w p ≤ M) (hv : ∀ x, v x ≤ M) (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (weightedFlatRepairCLM ρ w v A) ≤
      M * inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) := by
  rw [weightedFlatRepair_inner, flatGaugeHodgeK0_inner_right, mul_add]
  exact add_le_add (coordinateWeight_inner_le w M hw _) (coordinateWeight_inner_le v M hv _)

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

set_option maxHeartbeats 1200000 in
theorem weightedFlatRepair_coarse_estimate_false
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) (j : Fin d) (R : ℕ) (hR : 2 * R < n)
    (C : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] F) (Phi : F → ℝ) (hPhi : Phi 0 = 0)
    (w : PhysicalPlaquette d n → ℝ) (v : FinBox d n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ p, w p ≤ M) (hv : ∀ x, v x ≤ M) (c : ℝ)
    (hc : (1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) < c)
    (hdim : finrank ℝ F < 2 * (2 * R + 1) ^ d) :
    ¬ ∀ A : PhysicalGaugeOneCochain d n Nc,
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) +
        Phi (C A) + inner ℝ A (weightedFlatRepairCLM ρ w v A) := by
  intro hbound
  have hzeroRange : LinearMap.range
      (0 : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc) = ⊥ := by
    apply le_antisymm
    · rintro x ⟨y, hy⟩
      change x = 0
      change (0 : PhysicalGaugeOneCochain d n Nc) = x at hy
      exact hy.symm
    · exact bot_le
  have hdim' : finrank ℝ F + finrank ℝ (LinearMap.range
      (0 : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc)) <
      finrank ℝ (physicalCenteredFourierBand (n := n) hNc j R) := by
    simpa [hzeroRange, physicalCenteredFourierBand_finrank hNc j R hR] using hdim
  rcases exists_unseen_of_finrank_lt_measurement_add_repair
      (physicalCenteredFourierBand hNc j R) C
      (0 : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc) hdim'
    with ⟨A, hAS, hA, hCA, hz⟩
  have hlo := hbound A
  rw [hCA, hPhi, add_zero] at hlo
  have hweight := weightedFlatRepair_le_flat ρ w v M hw hv A
  have hband := physicalCenteredFourierBand_hodge_le hNc ρ j R hR A hAS
  have henergy : inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) +
      inner ℝ A (weightedFlatRepairCLM ρ w v A) ≤
      (1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) * ‖A‖ ^ 2 := by
    calc
      _ ≤ (1 + M) * inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) := by nlinarith
      _ ≤ (1 + M) * ((4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) * ‖A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hband (by linarith)
      _ = _ := by ring
  have hpos : 0 < ‖A‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hA)
  have hs := mul_lt_mul_of_pos_right hc hpos
  linarith
end Physical

local instance weightedSide_neZero (L N' : ℕ) [NeZero N'] : NeZero ((L + 1) * N') :=
  ⟨Nat.mul_ne_zero (Nat.succ_ne_zero L) (NeZero.ne N')⟩

set_option maxHeartbeats 1600000 in
theorem no_uniform_weightedFlatRepair
    {d Nc N' : ℕ} [NeZero d] [NeZero Nc] [NeZero N']
    {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) (j : Fin d)
    (C : ∀ L, RefinedPhysicalOneCochain d N' Nc L →ₗ[ℝ] F)
    (Phi : ℕ → F → ℝ) (hPhi : ∀ L, Phi L 0 = 0)
    (w : ∀ L, PhysicalPlaquette d ((L + 1) * N') → ℝ)
    (v : ∀ L, FinBox d ((L + 1) * N') → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ L p, w L p ≤ M) (hv : ∀ L x, v L x ≤ M) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ L (A : RefinedPhysicalOneCochain d N' Nc L),
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d ((L + 1) * N') Nc ρ A) +
        Phi L (C L A) + inner ℝ A (weightedFlatRepairCLM ρ (w L) (v L) A) := by
  rintro ⟨c, hc, hbound⟩
  let R := finrank ℝ F + 1
  have hfactor : 0 < 1 + M := by linarith
  obtain ⟨L, hR, hb⟩ := exists_refinement_below_threshold d N' R (c / (1 + M))
    (div_pos hc hfactor)
  have hb' : (1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 /
      ((((L + 1) * N' : ℕ) : ℝ) ^ 2)) < c := by
    simpa [mul_comm] using (lt_div_iff₀ hfactor).mp hb
  have hdim : finrank ℝ F < 2 * (2 * R + 1) ^ d := by
    simpa [R] using (physicalBand_budget_exceeded (d := d) (finrank ℝ F) 0)
  exact weightedFlatRepair_coarse_estimate_false hNc ρ j R hR (C L) (Phi L) (hPhi L)
    (w L) (v L) M hM (hw L) (hv L) c hb' hdim (hbound L)
end YangMills.RG
