import YangMills.RG.TorusPhysicalHodge
import YangMills.RG.CoarseMeasurementDimensionObstruction

/-! The actual physical real Fourier image has proved dimension and energy.
    The resulting finite flat rank obstruction assumes no comparison subspace. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero n]

noncomputable def centeredPhysicalBandMap (hNc : 2 ≤ Nc) (j : Fin d) (R : ℕ) :
    centeredFourierBand d n R →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc where
  toFun f := torusPhysicalEmbed hNc j f.val
  map_add' f g := torusPhysicalEmbed_add hNc j f.val g.val
  map_smul' r f := torusPhysicalEmbed_smul hNc j r f.val

theorem centeredPhysicalBandMap_injective (hNc : 2 ≤ Nc) (j : Fin d) (R : ℕ) :
    Function.Injective (centeredPhysicalBandMap (n := n) hNc j R) := by
  intro f g h
  apply Subtype.ext
  exact torusPhysicalEmbed_injective hNc j h

noncomputable def physicalCenteredFourierBand (hNc : 2 ≤ Nc) (j : Fin d) (R : ℕ) :
    Submodule ℝ (PhysicalGaugeOneCochain d n Nc) :=
  LinearMap.range (centeredPhysicalBandMap hNc j R)

theorem physicalCenteredFourierBand_finrank (hNc : 2 ≤ Nc) (j : Fin d)
    (R : ℕ) (hR : 2 * R < n) :
    finrank ℝ (physicalCenteredFourierBand (n := n) hNc j R) = 2 * (2 * R + 1) ^ d := by
  rw [physicalCenteredFourierBand,
    LinearMap.finrank_range_of_inj (centeredPhysicalBandMap_injective hNc j R),
    centeredFourierBand_finrank_real R hR]

set_option maxHeartbeats 800000 in
theorem physicalCenteredFourierBand_representation (hNc : 2 ≤ Nc) (j : Fin d)
    (R : ℕ) (A : PhysicalGaugeOneCochain d n Nc)
    (hA : A ∈ physicalCenteredFourierBand hNc j R) :
    ∃ c : (Fin d → Fin (2 * R + 1)) → ℂ,
      torusPhysicalEmbed hNc j
        (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x) = A := by
  classical
  rcases hA with ⟨f, hf⟩
  have hm : f.val ∈ Submodule.span ℂ
      (Set.range (centeredFourierProfile (d := d) (n := n) R)) := f.property
  rcases Submodule.mem_span_range_iff_exists_fun.mp hm with ⟨c, hc⟩
  have hs : (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x) = f.val := by
    calc
      _ = ∑ k, c k • centeredFourierProfile (d := d) (n := n) R k := by
        funext x
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = _ := hc
  refine ⟨c, ?_⟩
  rw [hs]
  exact hf

variable [NeZero d] [NeZero Nc]

set_option maxHeartbeats 800000 in
theorem physicalCenteredFourierBand_hodge_le (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (R : ℕ) (hR : 2 * R < n) (A : PhysicalGaugeOneCochain d n Nc)
    (hA : A ∈ physicalCenteredFourierBand hNc j R) :
    inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) ≤
      (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) * ‖A‖ ^ 2 := by
  rcases physicalCenteredFourierBand_representation hNc j R A hA with ⟨c, rfl⟩
  exact centeredFourier_physical_hodge_le hNc ρ j R hR c

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

set_option maxHeartbeats 1200000 in
theorem physicalCenteredFourierBand_coercivity_budget
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) (j : Fin d) (R : ℕ) (hR : 2 * R < n)
    (C : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] F)
    (V : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc)
    (Phi : F → ℝ) (hPhi : Phi 0 = 0) (c : ℝ)
    (hc : 4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2 < c)
    (hbound : ∀ A : PhysicalGaugeOneCochain d n Nc,
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) +
        Phi (C A) + inner ℝ A (V A)) :
    2 * (2 * R + 1) ^ d ≤ finrank ℝ F + finrank ℝ (LinearMap.range V) := by
  have h := factorized_coercivity_dimension_budget
    (physicalCenteredFourierBand (n := n) hNc j R) C V
    (fun A => inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A)) Phi hPhi
    (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) c hc
    (fun A hA => physicalCenteredFourierBand_hodge_le hNc ρ j R hR A hA) hbound
  rw [physicalCenteredFourierBand_finrank hNc j R hR] at h
  exact h

set_option maxHeartbeats 800000 in
theorem physicalCenteredFourierBand_coercivity_false
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) (j : Fin d) (R : ℕ) (hR : 2 * R < n)
    (C : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] F)
    (V : PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc)
    (Phi : F → ℝ) (hPhi : Phi 0 = 0) (c : ℝ)
    (hc : 4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2 < c)
    (hdim : finrank ℝ F + finrank ℝ (LinearMap.range V) < 2 * (2 * R + 1) ^ d) :
    ¬ ∀ A : PhysicalGaugeOneCochain d n Nc,
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) +
        Phi (C A) + inner ℝ A (V A) := by
  intro hbound
  have hb := physicalCenteredFourierBand_coercivity_budget hNc ρ j R hR C V Phi hPhi c hc hbound
  exact (not_le_of_gt hdim) hb

end YangMills.RG
