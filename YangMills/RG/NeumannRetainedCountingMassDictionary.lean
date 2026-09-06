import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernel
import YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge

/-!
PRE-VALIDATION: promoted source present; this module's .olean is not yet
materialized and this module path is not compiler-verified. Its draft passed
the HOT diagnostic recorded in ledger1129; a promoted cold gate is still required. This draft extracts the existing Hilbert-bundle transport argument
for the actual flat retained terminal counting mass. It imports no unverified
reflection draft and assumes no operator equality or family of flatness data.

Only the Q' counting-adjoint square is identified. In particular, this is NOT
an equality of Neumann and compressed-Dirichlet precisions, a regional inverse,
a reflection right-inverse law, a weighted-adjoint normalization or window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The source-generated flat weighted tower, with its counting adjoint,
has exactly the explicit counting mass after isometric codomain transport.
No positivity or value of spacing is substituted into the algebraic equality. -/
theorem neumannFlatGeneratedCountingMass_eq_explicit
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) (spacing : ℝ) :
    let T := regions.weightedQprimeTower hd hM rho spacing 0
      (cmp99SourceFlatGaugeConfig d N Nc)
      (cmp99SourceFlatZeroRadiusChain depth)
      cmp99SourceFlatGaugeConfig_zero_small
    T.Qprime.adjoint.comp T.Qprime =
      (regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
        (regions.flatExplicitQprime (Nc := Nc)) := by
  let background := cmp99SourceFlatGaugeConfig d N Nc
  let chain := cmp99SourceFlatZeroRadiusChain
    (d := d) (M := M) (Nc := Nc) depth
  let fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0 :=
    cmp99SourceFlatGaugeConfig_zero_small
  let T := regions.weightedQprimeTower hd hM rho spacing 0
    background chain fineSmall
  change T.Qprime.adjoint.comp T.Qprime =
    (regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
      (regions.flatExplicitQprime (Nc := Nc))
  let hT : T.TerminalSpace = regions.terminalHilbertSpace Nc :=
    regions.weightedQprimeTower_terminalSpace_eq hd hM rho spacing 0
      background chain fineSmall
  let hCoord : regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) :=
    regions.terminalHilbertSpace_eq_coordinate
  let Qtransported := cmp99SourceTerminalCLMTransport
    (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
    (F := T.TerminalSpace)
    (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
    (F' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
    rfl (hT.trans hCoord) T.Qprime
  have hphysical := regions.physicalQprime_eq_transported hd hM rho
    spacing 0 background chain fineSmall
  have hflat := regions.flatPhysicalQprime_eq_explicit hd hM rho spacing
  have hQ : regions.transportedQprime hd hM rho spacing 0
      background chain fineSmall = regions.flatExplicitQprime := by
    calc
      _ = regions.physicalQprime hd hM rho spacing 0
          background chain fineSmall := hphysical.symm
      _ = regions.flatPhysicalQprime hd hM rho spacing := rfl
      _ = regions.flatExplicitQprime := hflat
  have hQtransported : Qtransported = regions.flatExplicitQprime := hQ
  have htransported : Qtransported.adjoint.comp Qtransported =
      T.Qprime.adjoint.comp T.Qprime := by
    exact cmp99SourceTerminalCLMTransport_adjoint_comp_self
      (E := cmp99SourcePhysicalTerminalHilbertSpace Nc Omega)
      (F := T.TerminalSpace)
      (F' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
      (hT.trans hCoord) T.Qprime
  exact htransported.symm.trans
    (congrArg (fun Q => Q.adjoint.comp Q) hQtransported)

/-- Exact mass component of the internally generated retained terminal
prefix. Neither the Neumann Laplacian nor the physical scalar coefficient
is replaced by the generated compressed-precision constructor. -/
theorem neumannFlatRetainedTerminalCountingMass_eq_explicit
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) (spacing : ℝ) :
    let T := cmp99SourceFlatRetainedPhysicalTower hd hM rho Omega depth spacing
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    ((T.towerAt (Fin.last depth)).Qprime).adjoint.comp
        ((T.towerAt (Fin.last depth)).Qprime) =
      (regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
        (regions.flatExplicitQprime (Nc := Nc)) := by
  dsimp only
  rw [cmp99SourceFlatRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower]
  exact neumannFlatGeneratedCountingMass_eq_explicit
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth)
    hd hM rho spacing

end

end YangMills.RG
