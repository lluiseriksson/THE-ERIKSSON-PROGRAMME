import YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction
import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint

/-!
# One-scale analytic average and printed starred synthesis for CMP99 (3.59)

The analytically continued block average is complex-linear and carries the
literal source mass `M^{-d}`.  Its printed starred partner is constructed
independently with unit synthesis mass and inverse algebraic transport.  It
is deliberately not Lean's sesquilinear Hilbert `.adjoint` away from the real
slice.
-/

namespace YangMills.RG

noncomputable section

variable {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]

/-- Complex-linear transported block average with an explicit scalar mass. -/
noncomputable def cmp99ComplexTransportedBlockAverageCLM
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℂ g]
    [FiniteDimensional ℂ g]
    (Omega : ActiveGaugeRegion d (M * N')) (w : ℂ)
    (transport : FinBox d N' → FinBox d (M * N') → (g →L[ℂ] g)) :
    ActiveGaugeZeroCochain Omega g →L[ℂ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi =>
        WithLp.toLp 2 fun y =>
          w • ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
            transport y.1 x.1 (phi (cmp99ActiveFineSiteOfBlock Omega y x))
      map_add' := fun phi psi => by
        ext y
        simp only [PiLp.add_apply, map_add, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a phi => by
        ext y
        simp only [PiLp.smul_apply, map_smul, Finset.smul_sum,
          RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro x _
        simp only [smul_smul]
        rw [mul_comm w a] }

@[simp] theorem cmp99ComplexTransportedBlockAverageCLM_apply
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℂ g]
    [FiniteDimensional ℂ g]
    (Omega : ActiveGaugeRegion d (M * N')) (w : ℂ)
    (transport : FinBox d N' → FinBox d (M * N') → (g →L[ℂ] g))
    (phi : ActiveGaugeZeroCochain Omega g)
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    cmp99ComplexTransportedBlockAverageCLM Omega w transport phi y =
      w • ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
        transport y.1 x.1 (phi (cmp99ActiveFineSiteOfBlock Omega y x)) := by
  rfl

/-- Independent algebraic synthesis.  The caller supplies the printed
star-transport itself; no Hermitian adjoint is inferred. -/
noncomputable def cmp99ComplexTransportedBlockStarSynthesisCLM
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℂ g]
    [FiniteDimensional ℂ g]
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (starTransport : FinBox d N' → FinBox d (M * N') → (g →L[ℂ] g)) :
    ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g →L[ℂ]
      ActiveGaugeZeroCochain Omega g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun eta =>
        WithLp.toLp 2 fun x =>
          starTransport (blockSite M N' x.1) x.1
            (eta ⟨blockSite M N' x.1,
              (mem_cmp99ActiveCoarseRegion_sites_iff
                (M := M) (N' := N') Omega (blockSite M N' x.1)).2
                  (hOmega x.1 x.2)⟩)
      map_add' := fun eta theta => by
        ext x
        simp
      map_smul' := fun a eta => by
        ext x
        simp }

@[simp] theorem cmp99ComplexTransportedBlockStarSynthesisCLM_apply
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℂ g]
    [FiniteDimensional ℂ g]
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (starTransport : FinBox d N' → FinBox d (M * N') → (g →L[ℂ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g)
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99ComplexTransportedBlockStarSynthesisCLM Omega hOmega starTransport
        eta x =
      starTransport (blockSite M N' x.1) x.1
        (eta ⟨blockSite M N' x.1,
          (mem_cmp99ActiveCoarseRegion_sites_iff
            (M := M) (N' := N') Omega (blockSite M N' x.1)).2
              (hOmega x.1 x.2)⟩) := by
  rfl

/-- Literal forward adjoint transport of one analytically continued Wilson
line coefficient. -/
noncomputable def cmp99ComplexAdjointBlockTransport
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    FinBox d N' → FinBox d (M * N') →
      (SUNLieComplexCoord Nc →L[ℂ] SUNLieComplexCoord Nc) :=
  fun y x => LinearMap.toContinuousLinearMap
    (cmp99SpecialLinearAdjointCoordLM (holonomy y x))

/-- Printed starred transport: inverse algebraic conjugation, constructed
without calling a Hilbert adjoint. -/
noncomputable def cmp99ComplexAdjointBlockStarTransport
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    FinBox d N' → FinBox d (M * N') →
      (SUNLieComplexCoord Nc →L[ℂ] SUNLieComplexCoord Nc) :=
  fun y x => LinearMap.toContinuousLinearMap
    (cmp99SpecialLinearAdjointCoordLM (holonomy y x)⁻¹)

/-- The literal one-scale analytic `Q'(U)` factor of (3.19). -/
noncomputable def cmp99ComplexAdjointBlockAverageCLM
    (Omega : ActiveGaugeRegion d (M * N'))
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieComplexCoord Nc) :=
  cmp99ComplexTransportedBlockAverageCLM Omega
    (cmp99SourceBlockAverageWeight M d : ℂ)
    (cmp99ComplexAdjointBlockTransport holonomy)

/-- The literal one-scale analytic starred factor, with unit synthesis mass. -/
noncomputable def cmp99ComplexAdjointBlockStarSynthesisCLM
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99ComplexTransportedBlockStarSynthesisCLM Omega hOmega
    (cmp99ComplexAdjointBlockStarTransport holonomy)

end

end YangMills.RG
