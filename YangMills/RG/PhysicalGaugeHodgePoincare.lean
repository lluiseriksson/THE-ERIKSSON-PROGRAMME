import YangMills.RG.PhysicalGaugeCochains

/-!
# Full-periodic flat physical Hodge/block Poincare interface

This module records the full-periodic, trivial-background Poincare estimate
needed by the physical-cochain precision path.  It deliberately stays before
active-region boundary conventions, background-covariant block derivatives,
and Wilson-Hessian identification.

The source theorem is still external: `flatGaugeHodgePoincare` only repackages
a supplied curl/divergence/block estimate into the exact `K₀ + Q†Q` operator
interface already present in Lean.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- The full-periodic flat Hodge/block-Poincare estimate on physical
positive-bond one-cochains.

This is a physical-cochain proposition.  It does not identify `K₀` with the
Wilson Hessian and does not assert uniformity unless the supplied `CP` has
already been proved uniform. -/
def FlatGaugeHodgePoincare
    (d L N' Nc : ℕ)
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (CP : ℝ) : Prop :=
  0 < CP ∧
    ∀ A : FinePhysicalOneCochain d L N' Nc,
      ‖A‖ ^ 2 ≤
        CP *
          (inner ℝ A
              (flatGaugeHodgeK0CLM d (L * N') Nc ρ A)
            + ‖flatBlockConstraintQCLM
                  (d := d) (Nc := Nc) L N' A‖ ^ 2)

/-- Repackage a source-level curl/divergence/block estimate in terms of the
physical flat Hodge operator.

The mathematical content remains `hcurlDivBlock`: the volume-uniform
Poincare/Hodge estimate for the current line-integral block map is not proved
in this theorem. -/
theorem flatGaugeHodgePoincare
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    {CP : ℝ}
    (hCP : 0 < CP)
    (hcurlDivBlock :
      ∀ A : FinePhysicalOneCochain d L N' Nc,
        ‖A‖ ^ 2 ≤
          CP *
            (‖covariantD1CLM ρ
                  (trivialPhysicalGaugeBackground
                    d (L * N') Nc) A‖ ^ 2
              + ‖gaugeConstraintQCLM ρ
                  (trivialPhysicalGaugeBackground
                    d (L * N') Nc) A‖ ^ 2
              + ‖flatBlockConstraintQCLM
                    (d := d) (Nc := Nc) L N' A‖ ^ 2)) :
    FlatGaugeHodgePoincare d L N' Nc ρ CP := by
  refine ⟨hCP, ?_⟩
  intro A
  simpa only [flatGaugeHodgeK0_inner_right] using hcurlDivBlock A

end YangMills.RG
