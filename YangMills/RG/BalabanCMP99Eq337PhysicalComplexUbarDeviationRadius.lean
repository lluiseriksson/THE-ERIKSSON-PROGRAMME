import YangMills.RG.BalabanCMP99ComplexLocalizedUbarBackground
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexWilsonLineRadius

/-!
# Literal complex Eq. (3.37) radius for the source Ubar deviation

This leaf identifies all four factors of the source Ubar deviation with
literal Wilson paths.  The inverse coarse factor is not estimated through an
inverse norm: it is the holonomy of the reversed source parallel-transport
path by `OrientedLatticePath.holonomy_symm`.

The resulting bound retains the complex norm growth of every preceding
factor.  It does not import the unitary four-factor estimate.
-/

namespace YangMills.RG

open YangMills Matrix YangMills.GaugeConfig
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local notation "SLNc" => Matrix.SpecialLinearGroup (Fin Nc) ℂ

private theorem coe_eq_of_specialLinear_eq
    {A B : SLNc} (h : A = B) :
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) =
      (B : Matrix (Fin Nc) (Fin Nc) ℂ) :=
  congrArg Subtype.val h


private theorem coe_four_specialLinear_product
    (A : Fin 4 → SLNc) :
    ((((A 0 * A 1) * A 2) * A 3 : SLNc) :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      fourMatrixProduct (fun i =>
        (A i : Matrix (Fin Nc) (Fin Nc) ℂ)) := by
  simp only [fourMatrixProduct, Matrix.SpecialLinearGroup.coe_mul]

/-- The four literal fine paths in the printed source Ubar deviation.  The
fourth is the reversed straight fine representative of the positive coarse
bond. -/
def cmp99SourceComplexUbarFourPaths
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Fin 4 → List (ConcreteEdge d (M * N')) :=
  ![cmp99SourceUbarGamma1 (G := SUN Nc) b x,
    cmp99SourceUbarGamma2 (G := SUN Nc) b x,
    cmp99SourceUbarGamma3 (G := SUN Nc) b x,
    (cmp99SourceParallelTransportPath (G := SLNc)
      (blockBasepoint M N' b.1) b.2).symm.edges]

/-- All four source contours fit the same printed one-block length envelope.
The fourth case uses invariance of length under path reversal; no extra coarse
link is inserted. -/
theorem cmp99SourceComplexUbarFourPaths_length_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (i : Fin 4) :
    (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x i).length ≤
      d * (M - 1) := by
  fin_cases i
  · simpa [cmp99SourceComplexUbarFourPaths] using
      cmp99SourceUbarGamma1_length_le (G := SUN Nc) b x hx
  · simpa [cmp99SourceComplexUbarFourPaths] using
      cmp99SourceUbarGamma2_length_le (G := SUN Nc) hd hM b x
  · simpa [cmp99SourceComplexUbarFourPaths] using
      cmp99SourceUbarGamma3_length_le (G := SUN Nc) b x hx
  · change
      ((cmp99SourceParallelTransportPath (G := SLNc)
        (blockBasepoint M N' b.1) b.2).symm.edges).length ≤ d * (M - 1)
    simp only [OrientedLatticePath.symm, reverseLatticePath,
      List.length_reverse, List.length_map]
    exact cmp99SourceUbarGamma2_length_le (G := SLNc) hd hM b
      (blockBasepoint M N' b.1)

/-- Exact four-path identification.  In particular the last factor is not a
free coarse background and no equality between independently chosen
precisions or backgrounds is assumed. -/
theorem cmp99SourceComplexLocalizedUbarDeviation_coe_eq_fourPathProduct
    (background : GaugeConfig d (M * N') SLNc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    (cmp99SourceComplexLocalizedUbarDeviation background b x :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      fourMatrixProduct (fun i ↦
        ((wilsonLine background
            (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x i) : SLNc) :
          Matrix (Fin Nc) (Fin Nc) ℂ)) := by
  have hlast :
      (cmp99SourceBaseCoarseBackground background
          (positiveEdgeOfPhysicalBond b))⁻¹ =
        wilsonLine background
          (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x 3) := by
    rw [cmp99SourceBaseCoarseBackground_apply_pos]
    rw [← OrientedLatticePath.holonomy_symm]
    simp only [cmp99SourceComplexUbarFourPaths,
      OrientedLatticePath.holonomy]
    rfl
  have hgroupLiteral :
      cmp99SourceComplexLocalizedUbarDeviation background b x =
        wilsonLine background
            (cmp99SourceUbarGamma1 (G := SUN Nc) b x) *
          wilsonLine background
            (cmp99SourceUbarGamma2 (G := SUN Nc) b x) *
          wilsonLine background
            (cmp99SourceUbarGamma3 (G := SUN Nc) b x) *
          wilsonLine background
            (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x 3) := by
    unfold cmp99SourceComplexLocalizedUbarDeviation UbarDeviation
    dsimp only
    exact congrArg (fun z : SLNc =>
      wilsonLine background
          (cmp99SourceUbarGamma1 (G := SUN Nc) b x) *
        wilsonLine background
          (cmp99SourceUbarGamma2 (G := SUN Nc) b x) *
        wilsonLine background
          (cmp99SourceUbarGamma3 (G := SUN Nc) b x) * z) hlast
  let A : Fin 4 → SLNc := fun i =>
    wilsonLine background
      (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x i)
  have h0 : A 0 =
      wilsonLine background
        (cmp99SourceUbarGamma1 (G := SUN Nc) b x) := by
    change wilsonLine background
      (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x 0) =
        wilsonLine background
          (cmp99SourceUbarGamma1 (G := SUN Nc) b x)
    apply congrArg (wilsonLine background)
    simp [cmp99SourceComplexUbarFourPaths]
  have h1 : A 1 =
      wilsonLine background
        (cmp99SourceUbarGamma2 (G := SUN Nc) b x) := by
    change wilsonLine background
      (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x 1) =
        wilsonLine background
          (cmp99SourceUbarGamma2 (G := SUN Nc) b x)
    apply congrArg (wilsonLine background)
    simp [cmp99SourceComplexUbarFourPaths]
  have h2 : A 2 =
      wilsonLine background
        (cmp99SourceUbarGamma3 (G := SUN Nc) b x) := by
    change wilsonLine background
      (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x 2) =
        wilsonLine background
          (cmp99SourceUbarGamma3 (G := SUN Nc) b x)
    apply congrArg (wilsonLine background)
    simp [cmp99SourceComplexUbarFourPaths]
  have h3 : A 3 =
      wilsonLine background
        (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x 3) := by
    simp [A]
  have hgroup :
      cmp99SourceComplexLocalizedUbarDeviation background b x =
        ((A 0 * A 1) * A 2) * A 3 := by
    rw [h0, h1, h2, h3]
    exact hgroupLiteral
  change
    (cmp99SourceComplexLocalizedUbarDeviation background b x :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      fourMatrixProduct (fun i =>
        (A i : Matrix (Fin Nc) (Fin Nc) ℂ))
  exact (coe_eq_of_specialLinear_eq hgroup).trans
    (coe_four_specialLinear_product A)


/-- A uniform oriented-link radius produces the literal complex source-Ubar
budget with every path length and preceding factor norm visible. -/
theorem norm_cmp99SourceComplexLocalizedUbarDeviation_le_fourPathBudget
    (background : GaugeConfig d (M * N') SLNc)
    (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99ComplexFourWilsonPathDeviationBudget
        (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x) r := by
  rw [cmp99SourceComplexLocalizedUbarDeviation_coe_eq_fourPathProduct]
  exact norm_fourSpecialLinearWilsonLineProduct_sub_one_le
    (d := d) (N := M * N') (Nc := Nc)
    background (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x)
      r hr hlink

/-- Source-facing producer for the literal complex Eq. (3.37) background.
The only scalar input is the named oriented-link radius already derived from
the physical background and complex coordinate field. -/
theorem norm_cmp99Eq337SourceComplexLocalizedUbarDeviation_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d (M * N') Nc)
    (eta epsilonU rA : ℝ)
    (hr : 0 ≤
      cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    ‖(cmp99SourceComplexLocalizedUbarDeviation
        (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99ComplexFourWilsonPathDeviationBudget
        (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x)
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius
          Nc epsilonU eta rA) := by
  apply norm_cmp99SourceComplexLocalizedUbarDeviation_le_fourPathBudget
    _ _ hr
  exact
    norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
      U A eta epsilonU rA hA hsmall hU

/-- The literal scalar radius after replacing all four source-contour lengths
by the common printed one-block envelope. -/
def cmp99Eq337SourceComplexUbarUniformDeviationRadius
    (d M : ℕ) (r : ℝ) : ℝ :=
  cmp99ComplexFourWilsonUniformDeviationBudget (d * (M - 1)) r

/-- Fully source-facing uniform Ubar-deviation producer.  The output no longer
depends on the selected coarse bond or fine site. -/
theorem norm_cmp99Eq337SourceComplexLocalizedUbarDeviation_le_uniformRadius
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d (M * N') Nc)
    (eta epsilonU rA : ℝ)
    (hr : 0 ≤
      cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖(cmp99SourceComplexLocalizedUbarDeviation
        (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius
          Nc epsilonU eta rA) := by
  calc
    _ ≤ cmp99ComplexFourWilsonPathDeviationBudget
        (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x)
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius
          Nc epsilonU eta rA) :=
      norm_cmp99Eq337SourceComplexLocalizedUbarDeviation_le
        U A eta epsilonU rA hr hA hsmall hU b x
    _ ≤ cmp99Eq337SourceComplexUbarUniformDeviationRadius d M
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius
          Nc epsilonU eta rA) := by
      exact cmp99ComplexFourWilsonPathDeviationBudget_le_uniform
        (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x)
        (d * (M - 1))
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius
          Nc epsilonU eta rA) hr
        (cmp99SourceComplexUbarFourPaths_length_le hd hM b x hx)

/-- The uniform complex Ubar radius canonically produces the full Mercator
and no-winding budget once the one visible scalar gate is discharged. -/
noncomputable def cmp99Eq337SourceComplexUbarNoWindingBudget
    (d M Nc : ℕ) [NeZero Nc]
    (epsilonU eta rA : ℝ)
    (hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M
          (cmp99Eq337PhysicalComplexPerturbedLinkRadius
            Nc epsilonU eta rA) <
        cmp99UbarNoWindingThreshold Nc) :
    MatrixNearLogNoWindingBudget Nc :=
  cmp99PhysicalNoWindingBudget
    (cmp99Eq337SourceComplexUbarUniformDeviationRadius d M
      (cmp99Eq337PhysicalComplexPerturbedLinkRadius
        Nc epsilonU eta rA))
    hnoWinding

@[simp] theorem cmp99Eq337SourceComplexUbarNoWindingBudget_delta
    (d M Nc : ℕ) [NeZero Nc]
    (epsilonU eta rA : ℝ) (hnoWinding) :
    (cmp99Eq337SourceComplexUbarNoWindingBudget
      d M Nc epsilonU eta rA hnoWinding).δ =
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius
          Nc epsilonU eta rA) := by
  rfl

/-- One literal complex source RG step with the deviation certificate built
internally from Eq. (3.37).  Neither a preselected coarse background nor a
free Ubar-deviation family is accepted. -/
noncomputable def cmp99Eq337SourceComplexLocalizedNextBackground
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d (M * N') Nc)
    (eta epsilonU rA : ℝ)
    (hr : 0 ≤
      cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M
          (cmp99Eq337PhysicalComplexPerturbedLinkRadius
            Nc epsilonU eta rA) <
        cmp99UbarNoWindingThreshold Nc) :
    GaugeConfig d N' SLNc := by
  let background :=
    cmp99Eq337PhysicalComplexPerturbedBackground U A eta
  let B := cmp99Eq337SourceComplexUbarNoWindingBudget
    d M Nc epsilonU eta rA hnoWinding
  exact cmp99SourceComplexLocalizedNextBackground background B (by
    intro b x hx
    change ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ
    rw [show B.δ =
        cmp99Eq337SourceComplexUbarUniformDeviationRadius d M
          (cmp99Eq337PhysicalComplexPerturbedLinkRadius
            Nc epsilonU eta rA) by
      exact cmp99Eq337SourceComplexUbarNoWindingBudget_delta
        d M Nc epsilonU eta rA hnoWinding]
    exact
      norm_cmp99Eq337SourceComplexLocalizedUbarDeviation_le_uniformRadius
        hd hM U A eta epsilonU rA hr hA hsmall hU b x hx)

end

end YangMills.RG
