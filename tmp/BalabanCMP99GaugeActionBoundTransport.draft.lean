import YangMills.RG.BalabanCMP99CovariantD0GaugeIntertwiner
import YangMills.RG.FinitePiLpBlockLocalizedSupAlgebra

/-!
# PRE-VALIDATION: gauge transport of CMP99 localized action bounds

Source is present only in scratch.  No `.olean` has been materialized and no
declaration in this file has yet been verified by the Lean compiler.

This is the norm-and-support algebra of C6c.8e.  A pointwise linear isometry
preserves the finite supremum norm and every source-owner fibre.  Hence an
exact operator intertwiner transports a block-localized action bound with
the same amplitude, rate, owner maps, and distance.  No Green estimate or
operator covariance is accepted as an input in place of the intertwiner.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- A linear isometry of the whole finite field which is isometric at every
coordinate preserves the separate finite supremum norm exactly. -/
theorem finitePiLpSupNorm_linearIsometryEquiv_eq
    {ι g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (E : FinitePiLpField ι g ≃ₗᵢ[ℝ] FinitePiLpField ι g)
    (hE : ∀ (f : FinitePiLpField ι g) i, ‖E f i‖ = ‖f i‖)
    (f : FinitePiLpField ι g) :
    finitePiLpSupNorm (E f) = finitePiLpSupNorm f := by
  apply le_antisymm
  · apply finitePiLpSupNorm_le_of_norm_apply_le
    intro i
    rw [hE]
    exact norm_apply_le_finitePiLpSupNorm f i
  · have hback :
        finitePiLpSupNorm (E.symm (E f)) ≤ finitePiLpSupNorm (E f) := by
      apply finitePiLpSupNorm_le_of_norm_apply_le
      intro i
      have hpoint := hE (E.symm (E f)) i
      simp only [E.apply_symm_apply] at hpoint
      rw [← hpoint]
      exact norm_apply_le_finitePiLpSupNorm (E f) i
    simpa only [E.symm_apply_apply] using hback

/-- Pointwise isometry also preserves the exact owner-support condition.
Only the forward implication is needed for transport of a source estimate. -/
theorem finitePiLpSupportedInOwner_linearIsometryEquiv
    {ι β g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (E : FinitePiLpField ι g ≃ₗᵢ[ℝ] FinitePiLpField ι g)
    (hE : ∀ (f : FinitePiLpField ι g) i, ‖E f i‖ = ‖f i‖)
    (sourceOwner : ι → β) (owner : β)
    (f : FinitePiLpField ι g)
    (hf : FinitePiLpSupportedInOwner sourceOwner owner f) :
    FinitePiLpSupportedInOwner sourceOwner owner (E f) := by
  intro source hsource
  apply norm_eq_zero.mp
  rw [hE, hf source hsource, norm_zero]

/-- Exact conjugation by pointwise isometries transports a source-owner
localized action estimate without changing any displayed constant.

The hypothesis `hintertwines` is an operator theorem.  In the physical
specialization it is constructed from the covariant derivative, retained
average, precision, and inverse identities of C6c.8b--d; it is not a final
bound supplied by the caller. -/
theorem finitePiLpTypedBlockLocalizedSupBound_of_intertwines_isometries
    {ι κ β g : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T T' : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (Esource : FinitePiLpField ι g ≃ₗᵢ[ℝ] FinitePiLpField ι g)
    (Etarget : FinitePiLpField κ g ≃ₗᵢ[ℝ] FinitePiLpField κ g)
    (hsource : ∀ (f : FinitePiLpField ι g) i,
      ‖Esource f i‖ = ‖f i‖)
    (htarget : ∀ (f : FinitePiLpField κ g) i,
      ‖Etarget f i‖ = ‖f i‖)
    (hintertwines : T'.comp (Esource : _ →L[ℝ] _) =
      (Etarget : _ →L[ℝ] _).comp T)
    {sourceOwner : ι → β} {targetOwner : κ → β}
    {dist : β → β → ℕ} {A rate : ℝ}
    (hT' : FinitePiLpTypedBlockLocalizedSupBound T' sourceOwner
      targetOwner dist A rate) :
    FinitePiLpTypedBlockLocalizedSupBound T sourceOwner targetOwner
      dist A rate := by
  refine ⟨hT'.1, hT'.2.1, ?_⟩
  intro owner f hf target
  have hf' : FinitePiLpSupportedInOwner sourceOwner owner (Esource f) :=
    finitePiLpSupportedInOwner_linearIsometryEquiv
      Esource hsource sourceOwner owner f hf
  have hbound := hT'.2.2 owner (Esource f) hf' target
  have happ := congrArg
    (fun S : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g => S f)
    hintertwines
  change T' (Esource f) = Etarget (T f) at happ
  calc
    ‖T f target‖ = ‖T' (Esource f) target‖ := by
      rw [happ, htarget]
    _ ≤ A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm (Esource f) := hbound
    _ = A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) *
          finitePiLpSupNorm f := by
      rw [finitePiLpSupNorm_linearIsometryEquiv_eq Esource hsource]

/-- Intertwiners compose without changing orientation.  This is the exact
algebra used for `D G`, `G D*`, and `Delta G` after their individual
source-specific covariance theorems have been constructed. -/
theorem continuousLinearMap_comp_intertwines_isometries
    {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T1 T1' : F →L[ℝ] H) (T2 T2' : E →L[ℝ] F)
    (eE : E ≃ₗᵢ[ℝ] E) (eF : F ≃ₗᵢ[ℝ] F) (eH : H ≃ₗᵢ[ℝ] H)
    (h1 : T1'.comp (eF : F →L[ℝ] F) =
      (eH : H →L[ℝ] H).comp T1)
    (h2 : T2'.comp (eE : E →L[ℝ] E) =
      (eF : F →L[ℝ] F).comp T2) :
    (T1'.comp T2').comp (eE : E →L[ℝ] E) =
      (eH : H →L[ℝ] H).comp (T1.comp T2) := by
  calc
    (T1'.comp T2').comp (eE : E →L[ℝ] E) =
        T1'.comp (T2'.comp (eE : E →L[ℝ] E)) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = T1'.comp ((eF : F →L[ℝ] F).comp T2) := by rw [h2]
    _ = (T1'.comp (eF : F →L[ℝ] F)).comp T2 := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = ((eH : H →L[ℝ] H).comp T1).comp T2 := by rw [h1]
    _ = (eH : H →L[ℝ] H).comp (T1.comp T2) := by
      rw [ContinuousLinearMap.comp_assoc]

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The regional fine gauge action is pointwise isometric in the norm used
by the source-localized certificate. -/
theorem norm_cmp99RegionalFineGaugeLinearIsometryEquiv_apply_pointwise
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (f : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    ‖cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u f x‖ = ‖f x‖ := by
  rw [cmp99RegionalFineGaugeLinearIsometryEquiv_apply, rho.norm_ad]

/-- The source-based positive-bond gauge action is pointwise isometric in
the norm used by the derivative-action certificate. -/
theorem norm_cmp99PhysicalBondGaugeLinearIsometryEquiv_apply_pointwise
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (f : PhysicalGaugeOneCochain d N Nc)
    (b : PhysicalBond d N) :
    ‖cmp99PhysicalBondGaugeLinearIsometryEquiv rho u f b‖ = ‖f b‖ := by
  rw [cmp99PhysicalBondGaugeLinearIsometryEquiv_apply, rho.norm_ad]

end

end YangMills.RG
