import YangMills.RG.CoexactSubquadraticFamily

/-! A single scale is constructed from the common coefficient and repair cap.
Actual local maps and penalties remain explicit; the cutoff and the band
comparison are derived, not fields in a family certificate. -/
namespace YangMills.RG
open scoped RealInnerProductSpace

theorem coexact_dilation_scale_exists (d : ℕ) (M c : ℝ) (hc : 0 < c) :
    ∃ s : ℕ, (1 + M) * 4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) /
      ((s + 3 : ℕ) : ℝ) ^ 2 < c := by
  obtain ⟨s, hs⟩ := exists_nat_gt
    ((1 + M) * 4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) / c + 1)
  have hsq : (1 + M) * 4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) / c <
      ((s + 3 : ℕ) : ℝ) ^ 2 := by
    push_cast
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith [sq_nonneg (s : ℝ)]
  refine ⟨s, (div_lt_iff₀ (by positivity : (0 : ℝ) < ((s + 3 : ℕ) : ℝ) ^ 2)).2 ?_⟩
  have hmul := (div_lt_iff₀ hc).1 hsq
  nlinarith

theorem coexact_dilation_energy_identity (d s R : ℕ) (M : ℝ) :
    (1 + M) * (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * ((R + 1 : ℕ) : ℝ) ^ 2 /
      (((s + 3) * (R + 1) : ℕ) : ℝ) ^ 2) =
    (1 + M) * 4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) /
      ((s + 3 : ℕ) : ℝ) ^ 2 := by
  have hk : (s : ℝ) + 3 ≠ 0 := by positivity
  have hr : (R : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp [hk, hr] <;> ring

theorem coexact_band_power_bound (d r : ℕ) :
    (2 * r) ^ (d + 2) ≤ 2 * r * (2 * r + 1) ^ (d + 1) := by
  calc
    _ = (2 * r) * (2 * r) ^ (d + 1) := by
      rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := by gcongr <;> omega

section ActualDilation
variable {d Nc : ℕ} [NeZero Nc]
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (s R : ℕ)
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (M : ℝ) (hM : 0 ≤ M) (c : ℝ)
  (hscale : (1 + M) * 4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) /
    ((s + 3 : ℕ) : ℝ) ^ 2 < c)
variable (w : PhysicalGradientIndex (d + 2) ((s + 3) * (R + 1)) → ℝ)
  (hw : ∀ p, w p ≤ M)
variable (C : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc → F)
  (L : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc →L[ℝ] F)
  (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
variable (Phi : F → ℝ) (K delta r : ℝ) (hdelta : 0 < delta) (hr : 0 < r)
  (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
  (hbound : ∀ x : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc,
    gaugeConstraintQCLM rho
      (trivialPhysicalGaugeBackground (d + 2) ((s + 3) * (R + 1)) Nc) x = 0 →
    ‖x‖ < r → c * ‖x‖ ^ 2 ≤
      inner ℝ x (flatGaugeHodgeK0CLM (d + 2) ((s + 3) * (R + 1)) Nc rho x) +
      inner ℝ x (componentwiseWeightedRepairCLM w x) + Phi (C x))

include hNc rho M hM c hscale w hw C L hC hC0 Phi K delta r hdelta hr hPhi hbound

theorem coexactFlat_dilation_finrank_ge :
    2 * (R + 1) * (2 * (R + 1) + 1) ^ (d + 1) ≤ Module.finrank ℝ F := by
  have hcut : 2 * (R + 1) < (s + 3) * (R + 1) :=
    Nat.mul_lt_mul_of_pos_right (by omega : 2 < s + 3) (by omega)
  have hthreshold : (1 + M) *
      (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * ((R + 1 : ℕ) : ℝ) ^ 2 /
        (((s + 3) * (R + 1) : ℕ) : ℝ) ^ 2) < c := by
    rw [coexact_dilation_energy_identity]
    exact hscale
  by_contra hbad
  have hdim : Module.finrank ℝ F <
      2 * (R + 1) * (2 * (R + 1) + 1) ^ (d + 1) := Nat.lt_of_not_ge hbad
  exact (coexactFlat_local_coercivity_false hNc rho (R + 1) hcut w M hM hw
    C L hC hC0 Phi K delta r c hdelta hr hPhi hdim hthreshold) hbound

theorem coexactFlat_dilation_density :
    (2 / ((s + 3 : ℕ) : ℝ)) ^ (d + 2) *
      (((s + 3) * (R + 1) : ℕ) : ℝ) ^ (d + 2) ≤ (Module.finrank ℝ F : ℝ) := by
  have hb := coexactFlat_dilation_finrank_ge hNc rho s R F M hM c hscale
    w hw C L hC hC0 Phi K delta r hdelta hr hPhi hbound
  have hn := le_trans (coexact_band_power_bound d (R + 1)) hb
  have heq : (2 / ((s + 3 : ℕ) : ℝ)) ^ (d + 2) *
      (((s + 3) * (R + 1) : ℕ) : ℝ) ^ (d + 2) =
      (((2 * (R + 1) : ℕ) : ℝ)) ^ (d + 2) := by
    rw [← mul_pow]
    congr 1
    have hk : (s : ℝ) + 3 ≠ 0 := by positivity
    push_cast
    field_simp [hk] <;> ring
  rw [heq]
  exact_mod_cast hn
end ActualDilation

theorem coexactFlat_uniform_density_exists {d Nc : ℕ} [NeZero Nc]
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (M : ℝ) (hM : 0 ≤ M)
    (c : ℝ) (hc : 0 < c) :
    ∃ s : ℕ, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (R : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F]
        (w : PhysicalGradientIndex (d + 2) ((s + 3) * (R + 1)) → ℝ)
        (hw : ∀ p, w p ≤ M)
        (C : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc → F)
        (L : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc →L[ℝ] F)
        (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0) (Phi : F → ℝ)
        (K delta r : ℝ) (hdelta : 0 < delta) (hr : 0 < r)
        (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
        (hbound : ∀ x : PhysicalGaugeOneCochain (d + 2) ((s + 3) * (R + 1)) Nc,
          gaugeConstraintQCLM rho
            (trivialPhysicalGaugeBackground (d + 2) ((s + 3) * (R + 1)) Nc) x = 0 →
          ‖x‖ < r → c * ‖x‖ ^ 2 ≤
            inner ℝ x (flatGaugeHodgeK0CLM (d + 2) ((s + 3) * (R + 1)) Nc rho x) +
            inner ℝ x (componentwiseWeightedRepairCLM w x) + Phi (C x)),
        epsilon * (((s + 3) * (R + 1) : ℕ) : ℝ) ^ (d + 2) ≤
          (Module.finrank ℝ F : ℝ) := by
  obtain ⟨s, hs⟩ := coexact_dilation_scale_exists d M c hc
  refine ⟨s, (2 / ((s + 3 : ℕ) : ℝ)) ^ (d + 2), by positivity, ?_⟩
  intro R F _ _ _ w hw C L hC hC0 Phi K delta r hdelta hr hPhi hbound
  exact coexactFlat_dilation_density hNc rho s R F M hM c hs w hw C L hC hC0
    Phi K delta r hdelta hr hPhi hbound
end YangMills.RG
