import YangMills.RG.BalabanCMP99PatchedParametrixDefectDecay

/-!
# CMP99 patched parametrix: physical core partitions

A patched parametrix must not pay for the total number of local charts.  The
source-facing mechanism is that every physical bond belongs to exactly one
core.  Consequently every single-bond column of the patched defect contains
exactly one nonzero chart contribution.

This file packages that mechanism.  It proves both the exact resolution of the
identity by the core projections and the volume-independent exponential bound
for the complete patched defect.  It does not yet construct the geometric
cores or prove that the resulting defect has operator norm below one.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Every physical bond belongs to exactly one core among the selected
charts.  The explicit membership in `charts` prevents unused indices from
entering the partition statement. -/
def CMP99PhysicalCorePartition
    {ι : Type*} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (core : ι → Finset (PhysicalBond d N)) : Prop :=
  ∀ source, ∃ i, i ∈ charts ∧ source ∈ core i ∧
    ∀ j, j ∈ charts → source ∈ core j → j = i

/-- A physical core partition resolves the identity exactly. -/
theorem sum_physicalBondProjection_eq_id_of_corePartition
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (core : ι → Finset (PhysicalBond d N))
    (hpartition : CMP99PhysicalCorePartition charts core) :
    (∑ i ∈ charts,
        (physicalBondProjection (core i) : PhysicalEndomorphism d N Nc)) =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro source
  obtain ⟨i, hi, hsource, huniq⟩ := hpartition source
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.id_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · exact physicalBondProjection_apply_mem (core i) hsource x
  · intro j hj hji
    have hnot : source ∉ core j := by
      intro hjsource
      exact hji (huniq j hj hjsource)
    exact physicalBondProjection_apply_not_mem (core j) hnot x
  · intro hni
    exact (hni hi).elim

/-- A source-supported family of chart operators inherits a uniform kernel
bound without a factor `charts.card`: for each source only its unique core
contributes. -/
theorem physicalExponentialKernelBound_sum_of_corePartition
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (core : ι → Finset (PhysicalBond d N))
    (term : ι → PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 < rate)
    (hpartition : CMP99PhysicalCorePartition charts core)
    (hsupport : ∀ i, i ∈ charts → ∀ source (v : SUNLieCoord Nc),
      source ∉ core i →
        term i (singlePhysicalBondCochain source v) = 0)
    (hterm : ∀ i, i ∈ charts →
      PhysicalCovarianceExponentialKernelBound (term i) dist A rate) :
    PhysicalCovarianceExponentialKernelBound
      (∑ i ∈ charts, term i) dist A rate := by
  refine ⟨hA, hrate, ?_⟩
  intro source target v
  obtain ⟨i, hi, hsource, huniq⟩ := hpartition source
  have hcolumn :
      (∑ j ∈ charts, term j)
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) =
        term i (singlePhysicalBondCochain source v) := by
    apply PiLp.ext
    intro target
    simp only [ContinuousLinearMap.sum_apply]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      have hnot : source ∉ core j := by
        intro hjsource
        exact hji (huniq j hj hjsource)
      rw [hsupport j hj source v hnot]
      rfl
    · intro hni
      exact (hni hi).elim
  rw [hcolumn]
  exact (hterm i hi).2.2 source target v

/-- The exact patched identity with the resolution of the identity generated
internally from a physical core partition. -/
theorem comp_cmp99PatchedPhysicalParametrix_of_corePartition
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hpartition : CMP99PhysicalCorePartition charts core) :
    K.comp
        (cmp99PatchedPhysicalParametrix charts K enlarged core hc hmass hK) =
      ContinuousLinearMap.id ℝ _ +
        cmp99PatchedPhysicalParametrixDefect
          charts K enlarged core hc hmass hK :=
  comp_cmp99PatchedPhysicalParametrix charts K enlarged core hc hmass hK
    (sum_physicalBondProjection_eq_id_of_corePartition
      charts core hpartition)

/-- A uniform collar for a physical core partition gives the complete patched
defect the same exponentially small amplitude as one chart.  Exact source
partitioning removes any dependence on the number of charts. -/
theorem cmp99PatchedPhysicalParametrixDefect_exponentialKernelBound
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hpartition : CMP99PhysicalCorePartition charts core)
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {R NR L : ℕ} {M c mass κ σ Ssum : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ) (hSsum : 0 ≤ Ssum)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (- (σ * (dist x z : ℝ))) ≤ Ssum)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (R : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (hsep : ∀ i, i ∈ charts →
      CMP99CoreExteriorSeparated (core i) (enlarged i) dist L) :
    PhysicalCovarianceExponentialKernelBound
      (cmp99PatchedPhysicalParametrixDefect
        charts K enlarged core hc hmass hK)
      dist
      (cmp99SingleDefectDecayAmplitude M κ R c mass Ssum *
        Real.exp (-(((((κ - σ) - σ) - σ) / 2) * (L : ℝ))))
      ((((κ - σ) - σ) - σ) / 2) := by
  let rate : ℝ := ((κ - σ) - σ) - σ
  let A : ℝ := cmp99SingleDefectDecayAmplitude M κ R c mass Ssum
  have hrate : 0 < rate := by
    dsimp [rate]
    linarith
  have hA : 0 ≤ A := by
    dsimp [A, cmp99SingleDefectDecayAmplitude]
    have hmin : 0 < min c mass := lt_min hc hmass
    positivity
  apply physicalExponentialKernelBound_sum_of_corePartition
    charts core
    (fun i =>
      (K - cmp99LocalizedPhysicalPrecision K (enlarged i) mass).comp
        ((cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK).comp
          (physicalBondProjection (core i))))
    dist
    (mul_nonneg hA (Real.exp_pos _).le) (half_pos hrate) hpartition
  · intro i hi source v hsource
    simp only [ContinuousLinearMap.comp_apply]
    rw [physicalBondProjection_single_not_mem (core i) source v hsource,
      map_zero, map_zero]
  · intro i hi
    have hbase :=
      cmp99SinglePhysicalParametrixDefect_exponentialKernelBound
        K (hsub i hi) dist hsymm hself htri hM hc hmass hσ h3σκ
        hSsum hsum hrange hbound hK hNR htilt
    rw [cmp99SinglePhysicalParametrixDefect_eq_exterior_flux
      K (hsub i hi) hc hmass hK] at hbase ⊢
    simpa [A, rate, ContinuousLinearMap.comp_assoc] using
      (physicalExteriorCoreKernelBound_of_separated
        (K.comp
          (cmp99LocalizedPhysicalCovariance
            K (enlarged i) hc hmass hK))
        (core i) (enlarged i) dist hbase (hsep i hi))

end

end YangMills.RG
