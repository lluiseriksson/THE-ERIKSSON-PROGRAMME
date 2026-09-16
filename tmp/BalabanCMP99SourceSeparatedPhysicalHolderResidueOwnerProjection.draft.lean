/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H5e0: the forward affine lift used by the generated physical Holder series
projects to the literal target-minus-coarse-block-basepoint endpoint.  The
zero-residue subtype is consumed through its named quotient theorem; it is
not discarded as an informal congruence.  Carrier transport to the separated
CMP99 presentation, owner bounds, B0 and window 15 remain open.
-/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift

namespace YangMills.RG

noncomputable section

/-- Every H5 affine zero-residue lift has exactly the periodic endpoint cast
required by H4d's residue-stable interface. -/
theorem
    cmp99SourceSeparatedPhysicalHolderForwardAffineResidue_cast_eq_target_sub_blockBasepoint_draft
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) (bondNu : Fin d)
    (n : CMP99FlatIntegerResidueClass d N 0) (nu : Fin d) :
    let u : Fin d → ℤ := fun k =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y k
    let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
    (cmp89SignedLatticeResidueAffineMap M forwardU n.1 nu : ZMod (M * N)) =
      (((x.shift bondNu nu).val : ZMod (M * N)) -
        ((blockBasepoint M N y nu).val : ZMod (M * N))) := by
  dsimp only
  let e := cmp99SourceSeparatedFineTargetShiftResidueEquiv x bondNu
  have hforward := congrFun
    (cmp99SourceSeparatedFineTargetShift_affineResidue_eq_forward_draft
      x y bondNu n) nu
  have hn := cmp99FlatIntegerZeroResidueClassQuotient_spec (e n) nu
  rw [← hforward, ← hn]
  simp only [cmp89SignedLatticeResidueAffineMap,
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement, blockBasepoint]
  push_cast
  ring

/-- The unshifted base of the forward affine fibre already has the same
periodic endpoint.  This is obtained from the zero element of the exact
zero-residue subtype, not by forgetting the subtype. -/
theorem
    cmp99SourceSeparatedPhysicalHolderForwardBase_cast_eq_target_sub_blockBasepoint_draft
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) (bondNu nu : Fin d) :
    let u : Fin d → ℤ := fun k =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y k
    let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
    (forwardU nu : ZMod (M * N)) =
      (((x.shift bondNu nu).val : ZMod (M * N)) -
        ((blockBasepoint M N y nu).val : ZMod (M * N))) := by
  dsimp only
  let zeroResidue : CMP99FlatIntegerResidueClass d N 0 :=
    ⟨fun _ => 0, by rfl⟩
  have h :=
    cmp99SourceSeparatedPhysicalHolderForwardAffineResidue_cast_eq_target_sub_blockBasepoint_draft
      x y bondNu zeroResidue nu
  simpa [zeroResidue, cmp89SignedLatticeResidueAffineMap] using h

/-- Centering the forward endpoint modulo the full fine period preserves the
same physical endpoint cast.  This is the residual weight left by the exact
zero-residue `tsum` bound and hence the lift consumed by H4d. -/
theorem
    cmp99SourceSeparatedPhysicalHolderCenteredForwardBase_cast_eq_target_sub_blockBasepoint_draft
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) (bondNu nu : Fin d) :
    let u : Fin d → ℤ := fun k =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y k
    let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
    (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N) forwardU nu :
        ZMod (M * N)) =
      (((x.shift bondNu nu).val : ZMod (M * N)) -
        ((blockBasepoint M N y nu).val : ZMod (M * N))) := by
  dsimp only
  rw [cmp99CenteredPeriodicEndpointRepresentative_cast_eq]
  exact
    cmp99SourceSeparatedPhysicalHolderForwardBase_cast_eq_target_sub_blockBasepoint_draft
      x y bondNu nu

end

end YangMills.RG
