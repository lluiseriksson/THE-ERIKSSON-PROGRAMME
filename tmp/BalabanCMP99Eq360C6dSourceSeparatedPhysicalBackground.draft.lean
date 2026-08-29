import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen
import YangMills.RG.BalabanCMP99Eq389ThreeSpeciesPhysicalBound

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.

# Literal C6d background on the source-separated carrier

The regional C6d precision uses the transformed background produced by the
regular-cube witness.  This module transports exactly that background across
the printed carrier equality.  No independent background is caller data.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification
  (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
variable {U : PhysicalGaugeBackground 4
  (L ^ (depth + 1) * (2 * (K * Q))) Nc}
variable {eta alpha0 alpha1 : ℝ}

/-- Casting a finite torus across an equality of side lengths commutes with
one positive lattice step.  This is exposed publicly for the C6d background
stencil instead of relying on an incidental simplifier reduction. -/
theorem finBoxCast_shift_c6d
    {d N M : ℕ} [NeZero N] [NeZero M]
    (h : N = M) (x : FinBox d N) (i : Fin d) :
    Equiv.cast (congrArg (FinBox d) h) (x.shift i) =
      (Equiv.cast (congrArg (FinBox d) h) x).shift i := by
  subst M
  rfl

/-- The unique source-carrier background used by the derived Eq. (3.42)
actions for the literal C6d precision. -/
noncomputable def cmp99Eq360C6dSourceSeparatedPhysicalBackground
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q))
      (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube
      (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n Mlarge
      scaleExtent S scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1) :
    PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc :=
  cmp99Eq389SourceSeparatedPhysicalBackground L K Q depth Nc
    (R.toCubeWitness C alpha1 hscale).transformedBackground

/-- The value-level transport is exposed so later stencil proofs cannot
silently switch to the technical retained extension or to a free background.
-/
theorem cmp99Eq360C6dSourceSeparatedPhysicalBackground_apply
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q))
      (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube
      (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n Mlarge
      scaleExtent S scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    (edge : ConcreteEdge 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99Eq360C6dSourceSeparatedPhysicalBackground R C hscale edge =
      (R.toCubeWitness C alpha1 hscale).transformedBackground
        { source :=
            (cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier
              L K Q depth).symm ▸ edge.source
          dir := edge.dir
          sign := edge.sign } := by
  rfl

/-- The exact carrier transport used by the C6d background preserves a
positive fine step. -/
theorem cmp99Eq360C6dSourceSeparatedPhysicalBackground_cast_shift
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (i : Fin 4) :
    (cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier
        L K Q depth).symm ▸ (x.shift i) =
      ((cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier
        L K Q depth).symm ▸ x).shift i := by
  exact finBoxCast_shift_c6d
    (cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier
      L K Q depth).symm x i

end

end YangMills.RG
