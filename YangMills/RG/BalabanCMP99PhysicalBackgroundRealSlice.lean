import YangMills.RG.BalabanCMP99Eq359OneScaleRealSlice
import YangMills.RG.BalabanCMP99ComplexPhysicalRegionalTower

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Physical background and contour holonomy on the compact real slice

This leaf embeds a complete physical gauge background into `SL(N,C)` and
proves that the complex block-contour holonomy is the canonical image of the
physical holonomy.  The equality uses the exact shared edge list fixed by
`cmp99SpecialLinearBlockContainedContourSystem`; no contour equality is
caller data.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Canonical pointwise embedding of a physical gauge background. -/
def cmp99PhysicalGaugeBackgroundToSpecialLinear
    (U : PhysicalGaugeBackground d N Nc) :
    GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ) where
  toFun e := cmp99SUNToSpecialLinear Nc (U e)
  map_reverse e := by
    change cmp99SUNToSpecialLinear Nc
        (U (FiniteLatticeGeometry.reverse e)) =
      (cmp99SUNToSpecialLinear Nc (U e))⁻¹
    rw [GaugeConfig.map_reverse, map_inv]

@[simp] theorem cmp99PhysicalGaugeBackgroundToSpecialLinear_apply
    (U : PhysicalGaugeBackground d N Nc)
    (e : FiniteLatticeGeometry.E
      (d := d) (N := N) (G := SUN Nc)) :
    cmp99PhysicalGaugeBackgroundToSpecialLinear U e =
      cmp99SUNToSpecialLinear Nc (U e) := rfl

/-- Ordered products commute with the canonical compact-to-complex group
embedding. -/
theorem wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear
    (U : PhysicalGaugeBackground d N Nc)
    (es : List (FiniteLatticeGeometry.E
      (d := d) (N := N) (G := SUN Nc))) :
    wilsonLine (cmp99PhysicalGaugeBackgroundToSpecialLinear U) es =
      cmp99SUNToSpecialLinear Nc (wilsonLine U es) := by
  induction es with
  | nil => simp
  | cons e es ih =>
      rw [wilsonLine_cons, wilsonLine_cons,
        cmp99PhysicalGaugeBackgroundToSpecialLinear_apply, ih, map_mul]

variable {M N' : ℕ} [NeZero M] [NeZero N']

/-- The analytic block holonomy restricts to the exact physical contour
holonomy on every compact background. -/
theorem cmp99ComplexPhysicalBlockHolonomy_realSlice
    (U : PhysicalGaugeBackground d (M * N') Nc) :
    cmp99ComplexPhysicalBlockHolonomy
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U) =
      cmp99SUNHolonomyToSpecialLinear
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc)) U) := by
  funext y x
  let physical := cmp99BlockContainedContourSystem (G := SUN Nc) y x
  change wilsonLine (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
      physical.edges =
    cmp99SUNToSpecialLinear Nc (wilsonLine U physical.edges)
  exact wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear U physical.edges

/-- For a real physical one-cochain and real parameter, the complete
oriented complex perturbation is exactly the canonical embedding of the
physical `SU(N)` left variation.  Negative links follow by inversion; no
second background is supplied by the caller. -/
theorem cmp99Eq337PhysicalComplexPerturbedBackground_realSlice
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (eta : ℝ) :
    cmp99Eq337PhysicalComplexPerturbedBackground U
        (cmp99Eq337PhysicalComplexifyOneCochain A) eta =
      cmp99PhysicalGaugeBackgroundToSpecialLinear
        (cmp98PhysicalSuLeftVariation U A eta) := by
  have hpos : ∀ b : PhysicalBond d (M * N'),
      cmp99Eq337PhysicalComplexPerturbedPositiveBondSL U
          (cmp99Eq337PhysicalComplexifyOneCochain A) eta b =
        cmp99SUNToSpecialLinear Nc
          (cmp98PhysicalSuLeftVariation U A eta
            (positiveEdgeOfPhysicalBond b)) := by
    intro b
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrArg (fun Z ↦ Z i j)
      (cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_realSlice
        U A eta b)
  apply gaugeConfig_ext
  intro e
  cases e with
  | mk x i sign =>
      cases sign
      · change
          (cmp99Eq337PhysicalComplexPerturbedPositiveBondSL U
              (cmp99Eq337PhysicalComplexifyOneCochain A) eta (x, i))⁻¹ =
            cmp99SUNToSpecialLinear Nc
              ((cmp98PhysicalSuLeftVariation U A eta
                (positiveEdgeOfPhysicalBond (x, i)))⁻¹)
        rw [map_inv, hpos]
      · change
          cmp99Eq337PhysicalComplexPerturbedPositiveBondSL U
              (cmp99Eq337PhysicalComplexifyOneCochain A) eta (x, i) =
            cmp99SUNToSpecialLinear Nc
              (cmp98PhysicalSuLeftVariation U A eta
                (positiveEdgeOfPhysicalBond (x, i)))
        exact hpos (x, i)

end

end YangMills.RG
