import YangMills.RG.BalabanCMP99SourceLocalizedTowerCanonicalExtension

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Canonical global extension of a locally small source background

The retained fine read carrier determines the only positive bonds inspected
by the localized tower.  This module keeps the given background on those
bonds and inserts the identity elsewhere.  The result is a complete globally
small gauge background produced internally, not an extension supplied by the
caller.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Canonical identity extension of the positive coordinates retained by the
exact recursive source carrier.  Negative coordinates are reconstructed by
the standard gauge-configuration convention. -/
noncomputable def CMP99SourceActiveRegionChain.retainedFineExtension
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (background : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeBackground d N Nc := by
  classical
  exact gaugeConfigOfPositiveBonds fun b =>
    if b ∈ regions.retainedFineReadBonds (Nc := Nc) then
      background (positiveEdgeOfPhysicalBond b)
    else 1

@[simp] theorem CMP99SourceActiveRegionChain.retainedFineExtension_apply_pos_of_mem
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (background : PhysicalGaugeBackground d N Nc)
    (b : PhysicalBond d N)
    (hb : b ∈ regions.retainedFineReadBonds (Nc := Nc)) :
    regions.retainedFineExtension background (positiveEdgeOfPhysicalBond b) =
      background (positiveEdgeOfPhysicalBond b) := by
  classical
  rw [CMP99SourceActiveRegionChain.retainedFineExtension,
    gaugeConfigOfPositiveBonds_apply_pos, if_pos hb]

@[simp] theorem CMP99SourceActiveRegionChain.retainedFineExtension_apply_pos_of_not_mem
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (background : PhysicalGaugeBackground d N Nc)
    (b : PhysicalBond d N)
    (hb : b ∉ regions.retainedFineReadBonds (Nc := Nc)) :
    regions.retainedFineExtension background (positiveEdgeOfPhysicalBond b) =
      1 := by
  classical
  rw [CMP99SourceActiveRegionChain.retainedFineExtension,
    gaugeConfigOfPositiveBonds_apply_pos, if_neg hb]

/-- Local smallness on the exact retained carrier becomes global smallness of
the canonical identity extension. -/
theorem CMP99SourceActiveRegionChain.norm_retainedFineExtension_sub_one_le
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (background : PhysicalGaugeBackground d N Nc)
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ∀ e : ConcreteEdge d N,
      ‖(regions.retainedFineExtension background e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon := by
  intro e
  rcases e with ⟨y, mu, orient⟩
  cases orient with
  | false =>
      rw [CMP99SourceActiveRegionChain.retainedFineExtension,
        gaugeConfigOfPositiveBonds_apply_neg]
      exact (norm_sun_inv_sub_one_le _).trans (by
        by_cases hb : (y, mu) ∈ regions.retainedFineReadBonds (Nc := Nc)
        · rw [if_pos hb]
          exact localSmall (y, mu) hb
        · rw [if_neg hb]
          simpa only [map_one, sub_self, norm_zero] using epsilon_nonneg)
  | true =>
      by_cases hb : (y, mu) ∈ regions.retainedFineReadBonds (Nc := Nc)
      · rw [regions.retainedFineExtension_apply_pos_of_mem background (y, mu) hb]
        exact localSmall (y, mu) hb
      · rw [regions.retainedFineExtension_apply_pos_of_not_mem
          background (y, mu) hb]
        simpa only [map_one, sub_self, norm_zero] using epsilon_nonneg

/-- The localized tower equals the canonical source tower of the internally
constructed retained identity extension.  No extension or global-smallness
certificate is supplied by the caller. -/
theorem CMP99SourceActiveRegionChain.localizedWeightedQprimeTower_Qprime_eq_retainedFineExtension
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : PhysicalGaugeBackground d N Nc)
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (localSmall : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let extension := regions.retainedFineExtension background
    let extensionSmall := regions.norm_retainedFineExtension_sub_one_le
      background epsilon chain.epsilon_nonneg localSmall
    (regions.localizedWeightedQprimeTower hd hM rho spacing epsilon background
        chain localSmall).Qprime =
      (regions.weightedQprimeTower hd hM rho spacing epsilon extension chain
        extensionSmall).Qprime := by
  letI : NeZero N := regions.neZero
  dsimp only
  apply regions.localizedWeightedQprimeTower_Qprime_eq_canonicalExtension
    hd hM rho spacing epsilon background
      (regions.retainedFineExtension background) chain localSmall
      (regions.norm_retainedFineExtension_sub_one_le background epsilon
        chain.epsilon_nonneg localSmall)
  intro q hq
  exact (regions.retainedFineExtension_apply_pos_of_mem background q hq).symm

end

end YangMills.RG
