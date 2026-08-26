import tmp.BalabanCMP99Eq359OneScaleRealSlice.draft
import tmp.BalabanCMP99ComplexPhysicalRegionalTower.draft

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

end

end YangMills.RG
