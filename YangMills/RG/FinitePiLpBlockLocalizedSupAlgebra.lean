/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99OneScaleRegionalPoincare
import YangMills.RG.FinitePiLpBlockLocalizedSup
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# PRE-VALIDATION: exact algebra for block-localized supremum bounds

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

CMP99 (3.42) and (3.89) act on an arbitrary field supported in one source
block.  This module records the elementary operations that preserve that
quantifier without expanding the field into coordinate probes: contractive
diagonal multiplication, regional restriction, and zero extension.

These are norm and support identities only.  They prove no physical Green
estimate, no three-species estimate, and no defect contraction.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The finite supremum norm is the least common upper bound of the
coordinate norms. -/
theorem finitePiLpSupNorm_le_of_norm_apply_le
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g]
    (f : FinitePiLpField ι g) {r : ℝ}
    (h : ∀ i, ‖f i‖ ≤ r) :
    finitePiLpSupNorm f ≤ r := by
  unfold finitePiLpSupNorm
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨i, _hi, rfl⟩
  exact h i

/-- A pointwise contractive scalar multiplier is contractive in the finite
supremum norm. -/
theorem finitePiLpSupNorm_scalarMultiplier_le
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (hh : ∀ i, ‖h i‖ ≤ 1)
    (f : FinitePiLpField ι g) :
    finitePiLpSupNorm (finitePiLpScalarMultiplier (g := g) h f) ≤
      finitePiLpSupNorm f := by
  apply finitePiLpSupNorm_le_of_norm_apply_le
  intro i
  rw [finitePiLpScalarMultiplier_apply, norm_smul]
  calc
    ‖h i‖ * ‖f i‖ ≤ 1 * ‖f i‖ :=
      mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)
    _ = ‖f i‖ := one_mul _
    _ ≤ finitePiLpSupNorm f := norm_apply_le_finitePiLpSupNorm f i

/-- A diagonal multiplier preserves support in every owner fibre. -/
theorem finitePiLpSupportedInOwner_scalarMultiplier
    {ι β g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (sourceOwner : ι → β) (owner : β) (h : ι → ℝ)
    (f : FinitePiLpField ι g)
    (hf : FinitePiLpSupportedInOwner sourceOwner owner f) :
    FinitePiLpSupportedInOwner sourceOwner owner
      (finitePiLpScalarMultiplier (g := g) h f) := by
  intro source hsource
  rw [finitePiLpScalarMultiplier_apply, hf source hsource]
  simp

/-- A contractive multiplier on the source side preserves a block-localized
supremum estimate without a fibre-cardinality factor. -/
theorem finitePiLpTypedBlockLocalizedSupBound_comp_scalarMultiplier_right
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    {sourceOwner : ι → β} {targetOwner : κ → β}
    {dist : β → β → ℕ} {A rate : ℝ}
    (hh : ∀ source, ‖h source‖ ≤ 1)
    (hC : FinitePiLpTypedBlockLocalizedSupBound C sourceOwner targetOwner
      dist A rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      (C.comp (finitePiLpScalarMultiplier (g := g) h))
      sourceOwner targetOwner dist A rate := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro owner f hf target
  have hsupport := finitePiLpSupportedInOwner_scalarMultiplier
    sourceOwner owner h f hf
  have hbound := hC.2.2 owner
    (finitePiLpScalarMultiplier (g := g) h f) hsupport target
  rw [ContinuousLinearMap.comp_apply]
  calc
    ‖C (finitePiLpScalarMultiplier (g := g) h f) target‖ ≤
        A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm (finitePiLpScalarMultiplier (g := g) h f) :=
      hbound
    _ ≤ A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by
      apply mul_le_mul_of_nonneg_left
      · exact finitePiLpSupNorm_scalarMultiplier_le h hh f
      · exact mul_nonneg hC.1 (Real.exp_pos _).le

/-- A uniformly bounded multiplier on the target side multiplies only the
displayed amplitude of a block-localized estimate. -/
theorem finitePiLpTypedBlockLocalizedSupBound_comp_scalarMultiplier_left
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : κ → ℝ) (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    {sourceOwner : ι → β} {targetOwner : κ → β}
    {dist : β → β → ℕ} {A B rate : ℝ}
    (hB : 0 ≤ B) (hh : ∀ target, ‖h target‖ ≤ B)
    (hC : FinitePiLpTypedBlockLocalizedSupBound C sourceOwner targetOwner
      dist A rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      ((finitePiLpScalarMultiplier (g := g) h).comp C)
      sourceOwner targetOwner dist (B * A) rate := by
  refine ⟨mul_nonneg hB hC.1, hC.2.1, ?_⟩
  intro owner f hf target
  have hbound := hC.2.2 owner f hf target
  rw [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
    norm_smul]
  calc
    ‖h target‖ * ‖C f target‖ ≤
        B * (A * Real.exp (-(rate *
          (dist (targetOwner target) owner : ℝ))) * finitePiLpSupNorm f) :=
      mul_le_mul (hh target) hbound (norm_nonneg _) hB
    _ = (B * A) * Real.exp (-(rate *
          (dist (targetOwner target) owner : ℝ))) * finitePiLpSupNorm f := by
      ring

/-- Regional restriction cannot increase the finite supremum norm. -/
theorem finitePiLpSupNorm_restrictZeroCLM_le
    {d N : ℕ} [NeZero N]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (f : GaugeZeroCochain d N g) :
    finitePiLpSupNorm (restrictZeroCLM (𝔤 := g) Omega f) ≤
      finitePiLpSupNorm f := by
  apply finitePiLpSupNorm_le_of_norm_apply_le
  intro x
  exact norm_apply_le_finitePiLpSupNorm f x.1

/-- Restriction transports a block-localized bound from an active source
carrier to the ambient source carrier using the literal site projection. -/
theorem finitePiLpTypedBlockLocalizedSupBound_comp_restrictZeroCLM_right
    {d N : ℕ} [NeZero N]
    {κ β g : Type*} [Fintype κ]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (C : ActiveGaugeZeroCochain Omega g →L[ℝ] FinitePiLpField κ g)
    (sourceOwner : FinBox d N → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) {A rate : ℝ}
    (hC : FinitePiLpTypedBlockLocalizedSupBound C
      (fun x : ActiveGaugeRegion.Site Omega => sourceOwner x.1)
      targetOwner dist A rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      (C.comp (restrictZeroCLM (𝔤 := g) Omega))
      sourceOwner targetOwner dist A rate := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro owner f hf target
  have hsupport : FinitePiLpSupportedInOwner
      (fun x : ActiveGaugeRegion.Site Omega => sourceOwner x.1) owner
      (restrictZeroCLM (𝔤 := g) Omega f) := by
    intro source hsource
    exact hf source.1 hsource
  have hbound := hC.2.2 owner (restrictZeroCLM (𝔤 := g) Omega f)
    hsupport target
  rw [ContinuousLinearMap.comp_apply]
  calc
    ‖C (restrictZeroCLM (𝔤 := g) Omega f) target‖ ≤
        A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm (restrictZeroCLM (𝔤 := g) Omega f) := hbound
    _ ≤ A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by
      apply mul_le_mul_of_nonneg_left
      · exact finitePiLpSupNorm_restrictZeroCLM_le Omega f
      · exact mul_nonneg hC.1 (Real.exp_pos _).le

/-- Zero extension cannot increase the finite supremum norm. -/
theorem finitePiLpSupNorm_extendZeroZeroCLM_le
    {d N : ℕ} [NeZero N]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (f : ActiveGaugeZeroCochain Omega g) :
    finitePiLpSupNorm (extendZeroZeroCLM Omega f) ≤ finitePiLpSupNorm f := by
  apply finitePiLpSupNorm_le_of_norm_apply_le
  intro x
  by_cases hx : x ∈ Omega.sites
  · rw [extendZeroZeroCLM_apply_of_mem Omega f x hx]
    exact norm_apply_le_finitePiLpSupNorm f ⟨x, hx⟩
  · rw [extendZeroZeroCLM_apply_of_not_mem Omega f x hx, norm_zero]
    exact finitePiLpSupNorm_nonneg f

/-- Zero extension transports a block-localized bound from an active target
carrier to the ambient target carrier.  Outside the region both sides of the
operator action vanish before any support hypothesis is used. -/
theorem finitePiLpTypedBlockLocalizedSupBound_extendZeroZeroCLM_left
    {d N : ℕ} [NeZero N]
    {ι β g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (C : FinitePiLpField ι g →L[ℝ] ActiveGaugeZeroCochain Omega g)
    (sourceOwner : ι → β) (targetOwner : FinBox d N → β)
    (dist : β → β → ℕ) {A rate : ℝ}
    (hC : FinitePiLpTypedBlockLocalizedSupBound C sourceOwner
      (fun x : ActiveGaugeRegion.Site Omega => targetOwner x.1)
      dist A rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      ((extendZeroZeroCLM Omega).comp C)
      sourceOwner targetOwner dist A rate := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro owner f hf target
  by_cases htarget : target ∈ Omega.sites
  · let activeTarget : ActiveGaugeRegion.Site Omega := ⟨target, htarget⟩
    have hbound := hC.2.2 owner f hf activeTarget
    simpa [ContinuousLinearMap.comp_apply,
      extendZeroZeroCLM_apply_of_mem Omega (C f) target htarget,
      activeTarget] using hbound
  · rw [ContinuousLinearMap.comp_apply,
      extendZeroZeroCLM_apply_of_not_mem Omega (C f) target htarget,
      norm_zero]
    exact mul_nonneg
      (mul_nonneg hC.1 (Real.exp_pos _).le)
      (finitePiLpSupNorm_nonneg f)

/-- Restriction, an active operator, and zero extension preserve the exact
ambient owner metric and amplitude. -/
theorem finitePiLpTypedBlockLocalizedSupBound_extend_comp_restrictZeroCLM
    {d N : ℕ} [NeZero N]
    {β g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (C : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    (ownerMap : FinBox d N → β) (dist : β → β → ℕ)
    {A rate : ℝ}
    (hC : FinitePiLpTypedBlockLocalizedSupBound C
      (fun x : ActiveGaugeRegion.Site Omega => ownerMap x.1)
      (fun x : ActiveGaugeRegion.Site Omega => ownerMap x.1)
      dist A rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      ((extendZeroZeroCLM Omega).comp
        (C.comp (restrictZeroCLM (𝔤 := g) Omega)))
      ownerMap ownerMap dist A rate := by
  apply finitePiLpTypedBlockLocalizedSupBound_extendZeroZeroCLM_left
  exact finitePiLpTypedBlockLocalizedSupBound_comp_restrictZeroCLM_right
    Omega C ownerMap
      (fun x : ActiveGaugeRegion.Site Omega => ownerMap x.1) dist hC

end

end YangMills.RG
