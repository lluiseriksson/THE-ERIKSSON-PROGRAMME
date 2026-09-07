import YangMills.RG.NeumannMixedImageReindex
import YangMills.RG.NeumannPhysicalFullFlag
import YangMills.RG.NeumannPhysicalMixedSummability
import YangMills.RG.NeumannPhysicalBoundaryTransfer

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. Do not run until the exact reindex prerequisite has passed.
The literal complex-valued physical Green and actual-carrier FULL flag are
constructed here, not supplied. Fine/block alignment remains explicit.
Seam and summability are not the infinite-lattice source equation, finite
operator interchange, regional inverse or window15.
-/

namespace YangMills.RG
noncomputable section

def neumannPhysicalMixedGreenSeries (N L j : ℕ) [NeZero L]
    (mass a : ℝ) (m target source : Fin 4 → ℤ) : ℂ :=
  ∑' p : (Fin 4 → ℤ) × (∀ i, neumannMixedBranch (neumannPhysicalFullFlag N m i)),
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
      (neumannMixedImage (neumannPhysicalFullFlag N m) m source p.1 p.2)

theorem summable_neumannPhysicalMixedGreenSeries
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (N : ℕ) (m : Fin 4 → ℤ) (hm : ∀ i, 0 < m i)
    (source : ∀ i, neumannImageIntervalPoint (m i)) (target : Fin 4 → ℤ) :
    Summable (fun p : (Fin 4 → ℤ) ×
      (∀ i, neumannMixedBranch (neumannPhysicalFullFlag N m i)) =>
        cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
          (neumannMixedImage (neumannPhysicalFullFlag N m) m
            (fun i => (source i).1) p.1 p.2)) := by
  exact summable_neumannActualFullGreen_mixedSource
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass
    (neumannPhysicalFullFlag N m) m hm source target

theorem neumannPhysicalMixedGreenSeries_periodic
    (N L j : ℕ) [NeZero L] (mass a : ℝ)
    (mu : Fin 4) (B : ℤ) (m target source : Fin 4 → ℤ)
    (hfull : Int.toNat (m mu) = N)
    (halign : m mu = ((L ^ j : ℕ) : ℤ) * B) :
    neumannPhysicalMixedGreenSeries N L j mass a m
      (fun i => if i = mu then target i + m mu else target i) source =
    neumannPhysicalMixedGreenSeries N L j mass a m target source := by
  have hflag : neumannPhysicalFullFlag N m mu = true :=
    (neumannPhysicalFullFlag_iff N m mu).2 hfull
  have ht : (fun i => target i + ((L ^ j : ℕ) : ℤ) *
      (if i = mu then B else 0)) =
      (fun i => if i = mu then target i + m mu else target i) := by
    funext i
    by_cases hi : i = mu
    · subst i
      simp only [if_true, ← halign]
    · simp [hi]
  have hs : ∀ y : Fin 4 → ℤ,
      (fun i => y i - ((L ^ j : ℕ) : ℤ) * (if i = mu then B else 0)) =
      (fun i => if i = mu then y i - m mu else y i) := by
    intro y
    funext i
    by_cases hi : i = mu
    · subst i
      simp only [if_true, ← halign]
    · simp [hi]
  unfold neumannPhysicalMixedGreenSeries
  calc
    _ = ∑' p : (Fin 4 → ℤ) ×
        (∀ i, neumannMixedBranch (neumannPhysicalFullFlag N m i)),
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
        (fun i => if i = mu then
          neumannMixedImage (neumannPhysicalFullFlag N m) m source p.1 p.2 i - m mu
          else neumannMixedImage (neumannPhysicalFullFlag N m) m source p.1 p.2 i) := by
      apply tsum_congr
      intro p
      have h := neumannPhysicalGreen_blockShiftTransfer L j mass a target
        (neumannMixedImage (neumannPhysicalFullFlag N m) m source p.1 p.2)
        (fun i => if i = mu then B else 0)
      rw [ht, hs] at h
      exact h
    _ = _ := neumannMixedImage_periodic_tsum (neumannPhysicalFullFlag N m)
      mu hflag m source (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target)

theorem neumannPhysicalMixedGreenSeries_properBoundary
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (N : ℕ) (mu : Fin 4) (c B : ℤ) (m target source : Fin 4 → ℤ)
    (hproper : Int.toNat (m mu) ≠ N)
    (halign : c * m mu = ((L ^ j : ℕ) : ℤ) * B) :
    neumannPhysicalMixedGreenSeries N L j mass a m
      (fun i => if i = mu then 2*c*m mu-1-target i else target i) source =
    neumannPhysicalMixedGreenSeries N L j mass a m target source := by
  have hflag : neumannPhysicalFullFlag N m mu = false := by
    simp [neumannPhysicalFullFlag, hproper]
  have hphase : 2 * ((L ^ j : ℕ) : ℤ) * B = 2*c*m mu := by
    calc
      _ = 2 * (((L ^ j : ℕ) : ℤ) * B) := by ring
      _ = 2 * (c * m mu) := by rw [halign]
      _ = _ := by ring
  unfold neumannPhysicalMixedGreenSeries
  calc
    _ = ∑' p : (Fin 4 → ℤ) ×
        (∀ i, neumannMixedBranch (neumannPhysicalFullFlag N m i)),
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
        (fun i => if i = mu then
          2*c*m mu-1-neumannMixedImage (neumannPhysicalFullFlag N m) m source p.1 p.2 i
          else neumannMixedImage (neumannPhysicalFullFlag N m) m source p.1 p.2 i) := by
      apply tsum_congr
      intro p
      simpa only [hphase] using
        neumannPhysicalGreen_blockBoundaryTransfer_massUniform
          ha hrho hamplitude hradius hdenWindow hpairWindow hmass
          mu B target (neumannMixedImage (neumannPhysicalFullFlag N m) m source p.1 p.2)
    _ = _ := neumannMixedImage_proper_tsum (neumannPhysicalFullFlag N m)
      mu hflag c m source (cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target)

end
end YangMills.RG

#print axioms YangMills.RG.summable_neumannPhysicalMixedGreenSeries
#print axioms YangMills.RG.neumannPhysicalMixedGreenSeries_periodic
#print axioms YangMills.RG.neumannPhysicalMixedGreenSeries_properBoundary
