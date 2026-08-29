import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen

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
actions for the literal C6d precision.  It is the direct pullback through the
same Step-7b equivalence that defines the ambient precision; no parallel
regional-size cast is substituted. -/
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
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let background := (R.toCubeWitness C alpha1 hscale).transformedBackground
  { toFun := fun edge => background
      { source := e edge.source
        dir := edge.dir
        sign := edge.sign }
    map_reverse := by
      intro edge
      cases edge with
      | mk source dir sign =>
          exact background.map_reverse
            { source := e source
              dir := dir
              sign := sign } }

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
            cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
              (L := L) (K := K) (Q := Q) (depth := depth) edge.source
          dir := edge.dir
          sign := edge.sign } := by
  rfl

/-- The exact Step-7b site equivalence preserves a positive fine step.  This
is the geometric input needed to transport the literal covariant stencil. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv_shift
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (i : Fin 4) :
    cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
        (L := L) (K := K) (Q := Q) (depth := depth) (x.shift i) =
      (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
        (L := L) (K := K) (Q := Q) (depth := depth) x).shift i := by
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  have happly (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
      cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
          (L := L) (K := K) (Q := Q) (depth := depth) y =
        cmp99GeneratedFineBoxOneBlockEquiv
          (d := 4) L (2 * (K * Q)) (depth + 1)
            (Equiv.cast (congrArg (FinBox 4) hsize.symm) y) := by
    rfl
  rw [happly (x.shift i), happly x]
  rw [finBoxCast_shift_c6d hsize.symm x i]
  exact cmp99GeneratedFineBoxOneBlockEquiv_shift
    (M := L) (N := 2 * (K * Q)) (depth + 1) (hsize.symm ▸ x) i

end

end YangMills.RG
