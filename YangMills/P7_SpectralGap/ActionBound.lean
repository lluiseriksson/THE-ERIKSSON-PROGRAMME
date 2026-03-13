import Mathlib
import YangMills.P7_SpectralGap.TransferMatrixGap

namespace YangMills

open MeasureTheory Real

/-! ## F7.2: Wilson Action Bound on Compact Groups

Key: use finBoxGeometry directly (universe 0) to match eriksson_phase7_spectralGap.
-/

variable {G : Type*} [Group G] [MeasurableSpace G]
variable [TopologicalSpace G] [CompactSpace G]

theorem plaquetteEnergy_bounded_above
    (plaquetteEnergy : G → ℝ) (hcont : Continuous plaquetteEnergy) :
    ∃ C : ℝ, ∀ g : G, plaquetteEnergy g ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun g => le_trans (le_abs_self _) (hC g (Set.mem_univ g))⟩

/-- wilsonAction bounded using finBoxGeometry (universe 0). -/
theorem wilsonAction_bounded_compact_box (d N : ℕ) [NeZero d] [NeZero N]
    (plaquetteEnergy : G → ℝ) (hcont : Continuous plaquetteEnergy) :
    ∃ S_bound : ℝ, 0 ≤ S_bound ∧
      ∀ A : @GaugeConfig d N G _ (finBoxGeometry d N G),
        wilsonAction plaquetteEnergy A ≤ S_bound := by
  obtain ⟨C, hC⟩ := plaquetteEnergy_bounded_above plaquetteEnergy hcont
  refine ⟨(Fintype.card (ConcretePlaquette d N) : ℝ) * (max C 0), by positivity, ?_⟩
  intro A
  -- finBoxGeometry.P = ConcretePlaquette definitionally
  show ∑ p : ConcretePlaquette d N, plaquetteEnergy (A.plaquetteHolonomy p) ≤ _
  calc ∑ p : ConcretePlaquette d N, plaquetteEnergy (A.plaquetteHolonomy p)
      ≤ ∑ _ : ConcretePlaquette d N, max C 0 :=
        Finset.sum_le_sum (fun p _ => le_trans (hC (A.plaquetteHolonomy p)) (le_max_left _ _))
    _ = (Fintype.card (ConcretePlaquette d N) : ℝ) * max C 0 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- F7.2 main: compact G + continuous energy + hdist → ClayYangMillsTheorem.
    hS DISCHARGED. Remaining: hdist and hm_phys. -/
theorem eriksson_phase7_actionBound (d N : ℕ) [NeZero d] [NeZero N]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N' : ℕ) → ConcretePlaquette d N' → ConcretePlaquette d N' → ℝ)
    (hβ : 0 ≤ β) (hcont : Continuous plaquetteEnergy)
    (m_phys : ℝ) (hm_phys : 0 < m_phys)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hdist : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      ∃ n : ℕ, distP N' p q = ↑n ∧
        |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ n - P₀‖) :
    ClayYangMillsTheorem := by
  obtain ⟨S_bound, hSb, hS⟩ := wilsonAction_bounded_compact_box d N plaquetteEnergy hcont
  exact eriksson_phase7_spectralGap μ plaquetteEnergy β F distP
    hβ S_bound m_phys hSb hS hm_phys nf ng hng T P₀ γ C_T hgap hdist

end YangMills
