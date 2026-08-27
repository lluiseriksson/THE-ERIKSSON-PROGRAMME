import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower
import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalPrecision

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.35): literal retained regional precision

This candidate installs the printed operator
`Delta'_a = Delta_U + a_j Q'^* Q'` on the exact source-region carrier.  The
regularity witness and retained tower are constructed internally.  No
precision, `Qprime`, coercivity estimate or Green operator is a caller input.
The regional derivative spacing is fixed to the same source `eta` appearing
in (3.35); a second unrelated spacing is not exposed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L N' M Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero N'] [NeZero M] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- Gauge precision is invariant when the terminal codomain bundle of `Qprime`
is transported explicitly and the transported map is then identified with the
canonical map.  The equality of Hilbert bundles is porting data, not a hidden
identification of two independently chosen precisions. -/
private theorem cmp99SourceGaugePrecision_eq_of_terminalCLMTransport
    {E F F' : CMP99SourceWeightedTowerHilbertSpace}
    (hF : F = F') (Delta : E.carrier →L[ℝ] E.carrier)
    (Q : E.carrier →L[ℝ] F.carrier)
    (Q' : E.carrier →L[ℝ] F'.carrier) (a : ℝ)
    (hQ : cmp99SourceTerminalCLMTransport rfl hF Q = Q') :
    cmp99SourceGaugePrecision Delta Q a =
      cmp99SourceGaugePrecision Delta Q' a := by
  subst F'
  change Q = Q' at hQ
  exact congrArg (fun R => cmp99SourceGaugePrecision Delta R a) hQ

/-- The literal regional precision on the terminal localized retained tower.
The coefficient `a_j` remains the printed flowing scalar. -/
noncomputable def
    CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (a_j : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  let W := R.toCubeWitness C alpha1 hscale
  let T := R.localizedRetainedTowerOfSourceRegion
    (spacing := eta) C hscale regions D hM rho halpha1 chain
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      Omega rho W.transformedBackground eta)
    (T.localizedTowerAt (Fin.last depth)).Qprime a_j

/-- The definition exposes the two printed summands without a shared or
renamed budget. -/
theorem
    CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision_eq
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (a_j : ℝ) :
    let W := R.toCubeWitness C alpha1 hscale
    let T := R.localizedRetainedTowerOfSourceRegion
      (spacing := eta) C hscale regions D hM rho halpha1 chain
    R.localizedRetainedPhysicalPrecision C hscale regions D hM rho halpha1
        chain a_j =
      cmp99ActiveRegionSourceCovariantLaplacian
          Omega rho W.transformedBackground eta +
        a_j • ((T.localizedTowerAt (Fin.last depth)).Qprime.adjoint.comp
          (T.localizedTowerAt (Fin.last depth)).Qprime) := by
  rfl

/-- The localized and canonical presentations are equal because their
terminal `Qprime` operators are proved equal by the retained-prefix
construction. -/
theorem
    CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision_eq_canonical
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (a_j : ℝ) :
    let W := R.toCubeWitness C alpha1 hscale
    let T := R.localizedRetainedTowerOfSourceRegion
      (spacing := eta) C hscale regions D hM rho halpha1 chain
    R.localizedRetainedPhysicalPrecision C hscale regions D hM rho halpha1
        chain a_j =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian
          Omega rho W.transformedBackground eta)
        (T.canonicalTowerAt (Fin.last depth)).Qprime a_j := by
  dsimp only [CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision]
  exact cmp99SourceGaugePrecision_eq_of_terminalCLMTransport
    (T.prefixTerminalSpace_eq (Fin.last depth))
    (cmp99ActiveRegionSourceCovariantLaplacian
      Omega rho W.transformedBackground eta)
    (T.localizedTowerAt (Fin.last depth)).Qprime
    (T.canonicalTowerAt (Fin.last depth)).Qprime a_j
    (T.prefixQprime_eq (Fin.last depth))

/-- Source-closed isolation of the Laplacian background change.  The
Corollary-3.6 region dictionary replaces the transformed-background
Laplacian by its exponential representative, while the retained-tower theorem
keeps the **same transformed-background terminal `Qprime`** in canonical
coordinates.  This is not yet CMP99 (3.59), which compares the two physical
`Qprime` towers and defines `F'_2(A)`.  No operator identification is accepted
from the caller. -/
theorem
    CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision_eq_exponentialSource
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (a_j : ℝ) :
    let W := R.toCubeWitness C alpha1 hscale
    let T := R.localizedRetainedTowerOfSourceRegion
      (spacing := eta) C hscale regions D hM (matrixSUNAdjointModel Nc)
        halpha1 chain
    R.localizedRetainedPhysicalPrecision C hscale regions D hM
        (matrixSUNAdjointModel Nc) halpha1 chain a_j =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc)
          (cmp99Eq335PhysicalExponentialBackground
            W.logarithmicRepresentative eta) eta)
        (T.canonicalTowerAt (Fin.last depth)).Qprime a_j := by
  rw [R.localizedRetainedPhysicalPrecision_eq_canonical
      (spacing := eta) C hscale regions D hM (matrixSUNAdjointModel Nc)
        halpha1 chain a_j,
    (R.toCubeWitness C alpha1 hscale).
      regionalLaplacian_eq_exponential_of_sourceRegionDictionary D]

/-- Self-adjointness is generated from the literal Laplacian and adjoint
mass; it is not an input to the source endpoint. -/
theorem
    CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision_isSymmetric
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (a_j : ℝ) :
    (R.localizedRetainedPhysicalPrecision C hscale regions D hM rho halpha1
      chain a_j).IsSymmetric := by
  unfold CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision
  apply cmp99SourceGaugePrecision_isSymmetric
  exact cmp99ActiveRegionSourceCovariantLaplacian_isSymmetric
    Omega rho (R.toCubeWitness C alpha1 hscale).transformedBackground eta

/-- Exact printed quadratic form on the physical regional carrier. -/
theorem
    CMP99Eq335PhysicalRegularityClass.inner_localizedRetainedPhysicalPrecision
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (a_j : ℝ) (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    let W := R.toCubeWitness C alpha1 hscale
    let T := R.localizedRetainedTowerOfSourceRegion
      (spacing := eta) C hscale regions D hM rho halpha1 chain
    inner ℝ phi
        (R.localizedRetainedPhysicalPrecision C hscale regions D hM rho
          halpha1 chain a_j phi) =
      ‖cmp99ActiveRegionSourceCovariantD0CLM
          Omega rho W.transformedBackground eta phi‖ ^ 2 +
        a_j * ‖(T.localizedTowerAt (Fin.last depth)).Qprime phi‖ ^ 2 := by
  dsimp only [CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision]
  rw [inner_cmp99SourceGaugePrecision,
    inner_cmp99ActiveRegionSourceCovariantLaplacian]

end

end YangMills.RG
