import YangMills.RG.BalabanCMP99FlatIntegerResidueClassDictionary
import YangMills.RG.BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary

/-!
# PRE-VALIDATION: arbitrary residue affine base to the literal fine-site owner metric

The generated full point-source identity selects the owner residue
`sourceOwner - targetOwner`.  After arbitrary-residue reindexing, its affine
base combines that owner lift with the two within-block endpoint
displacements.  This draft proves that the combined base has exactly the
periodic residue of the literal fine-site difference `source - target`, then
transports its centered `l1` weight to the existing diagonal owner estimate.

The proof does not identify signed antipodal representatives.  It also does
not yet bound the Green sum, prove CMP89 (2.42), construct uniform regional
`B0`/`delta0`, attain window 15, move `20/41`, or inhabit `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Multiplying congruent integers modulo `N` by `K` makes them congruent
modulo the full physical period `K*N`. -/
theorem intCast_mul_eq_intCast_mul_of_intCast_eq
    {K N : ℕ} [NeZero K] [NeZero N] {a b : ℤ}
    (h : ((a : ℤ) : ZMod N) = ((b : ℤ) : ZMod N)) :
    ((((K : ℤ) * a : ℤ) : ZMod (K * N))) =
      ((((K : ℤ) * b : ℤ) : ZMod (K * N))) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  calc
    (K : ℤ) * a - (K : ℤ) * b = (K : ℤ) * (a - b) := by ring
    _ = (K : ℤ) * ((N : ℤ) * c) := by rw [hc]
    _ = ((K * N : ℕ) : ℤ) * c := by push_cast; ring

/-- The canonical arbitrary-residue representative, lifted by the fine block
side, has the same full-period residue as any literal owner difference that
projects to the selected finite-grid residue. -/
theorem cmp99FlatIntegerResidueRepresentative_scaled_cast
    {d K N : ℕ} [NeZero K] [NeZero N]
    (r : CMP99FlatZModBox d N) (w : Fin d → ℤ)
    (hw : cmp99FlatIntegerResidue (N := N) w = r) (mu : Fin d) :
    (((((K : ℤ) * cmp99FlatIntegerResidueRepresentative r mu : ℤ) :
        ZMod (K * N)))) =
      (((((K : ℤ) * w mu : ℤ) : ZMod (K * N)))) := by
  apply intCast_mul_eq_intCast_mul_of_intCast_eq
  have hrmu := congrFun (cmp99FlatIntegerResidue_representative r) mu
  have hwmu := congrFun hw mu
  simpa [cmp99FlatIntegerResidue] using hrmu.trans hwmu.symm

/-- The selected owner residue in the generated full point-source formula. -/
def cmp99SourceGeneratedFlatPhysicalPointSourceOwnerResidue
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) : CMP99FlatZModBox d N :=
  cmp99FinBoxZModEquiv d N (blockSite K N source) -
    cmp99FinBoxZModEquiv d N (blockSite K N target)

/-- Affine base produced after reindexing the arbitrary owner residue.  The
two endpoint terms are exactly those appearing in the generated residue-class
composition, in its source/target orientation. -/
def cmp99SourceGeneratedFlatPhysicalPointSourceResidueAffineBase
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) : Fin d → ℤ :=
  let sourceOwner := blockSite K N source
  let targetOwner := blockSite K N target
  let r := cmp99SourceGeneratedFlatPhysicalPointSourceOwnerResidue source target
  fun mu ↦
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        K source sourceOwner mu -
      (-cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        K target targetOwner mu) +
      (K : ℤ) * cmp99FlatIntegerResidueRepresentative r mu

/-- The literal integer owner difference projects to the selected owner
residue. -/
theorem cmp99SourceGenerated_ownerDifference_residue
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) :
    cmp99FlatIntegerResidue (N := N)
        (fun mu ↦
          ((blockSite K N source mu).val : ℤ) -
            ((blockSite K N target mu).val : ℤ)) =
      cmp99SourceGeneratedFlatPhysicalPointSourceOwnerResidue source target := by
  funext mu
  simp [cmp99FlatIntegerResidue,
    cmp99SourceGeneratedFlatPhysicalPointSourceOwnerResidue,
    cmp99FinBoxZModEquiv_apply]

/-- The combined affine base projects to the literal fine-site difference
at the full physical period. -/
theorem cmp99SourceGenerated_residueAffineBase_cast_eq_source_sub_target
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) (mu : Fin d) :
    (((cmp99SourceGeneratedFlatPhysicalPointSourceResidueAffineBase
          source target mu : ℤ) : ZMod (K * N))) =
      ((source mu).val : ZMod (K * N)) -
        ((target mu).val : ZMod (K * N)) := by
  let sourceOwner := blockSite K N source
  let targetOwner := blockSite K N target
  let r := cmp99SourceGeneratedFlatPhysicalPointSourceOwnerResidue source target
  let w : Fin d → ℤ := fun nu ↦
    ((sourceOwner nu).val : ℤ) - ((targetOwner nu).val : ℤ)
  have hw : cmp99FlatIntegerResidue (N := N) w = r := by
    simpa [w, r, sourceOwner, targetOwner] using
      cmp99SourceGenerated_ownerDifference_residue source target
  have hscaled :=
    cmp99FlatIntegerResidueRepresentative_scaled_cast
      (K := K) r w hw mu
  change
    (((-cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          K source sourceOwner mu -
        (-cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          K target targetOwner mu) +
        (K : ℤ) * cmp99FlatIntegerResidueRepresentative r mu : ℤ) :
          ZMod (K * N))) = _
  simp only [cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement]
  rw [hscaled]
  push_cast
  simp [w, sourceOwner, targetOwner]
  ring

/-- Centering the combined affine base preserves exactly the `l1` length of
the shortest periodic fine-site displacement. -/
theorem cmp89Eq251LatticeL1Length_centered_generatedResidueAffineBase_eq_diagonal
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) :
    cmp89Eq251LatticeL1Length
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99SourceGeneratedFlatPhysicalPointSourceResidueAffineBase
            source target)) =
      cmp89Eq251LatticeL1Length
        (cmp99DiagonalPeriodicDisplacement source target) := by
  unfold cmp89Eq251LatticeL1Length
  apply Finset.sum_congr rfl
  intro mu _
  congr 1
  have hcenter :=
    cmp99CenteredPeriodicEndpointRepresentative_natAbs_eq_valMinAbs
      (K * N)
      (cmp99SourceGeneratedFlatPhysicalPointSourceResidueAffineBase
        source target mu)
  change
    (cmp99CenteredPeriodicEndpointRepresentative (K * N)
        (cmp99SourceGeneratedFlatPhysicalPointSourceResidueAffineBase
          source target mu)).1.natAbs =
      (cmp99DiagonalPeriodicDisplacement source target mu).natAbs
  rw [hcenter]
  unfold cmp99DiagonalPeriodicDisplacement
  unfold cmp116CMP89PeriodicCoordinateDisplacement
  exact congrArg (fun z : ZMod (K * N) ↦ z.valMinAbs.natAbs)
    (cmp99SourceGenerated_residueAffineBase_cast_eq_source_sub_target
      source target mu)

/-- The arbitrary-residue affine base has the exact diagonal periodic
exponential weight. -/
theorem cmp89SignedLatticeL1ExponentialWeight_centered_generatedResidueAffineBase_eq_diagonal
    {d K N : ℕ} [NeZero K] [NeZero N]
    (delta : ℝ) (source target : FinBox d (K * N)) :
    cmp89SignedLatticeL1ExponentialWeight delta
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99SourceGeneratedFlatPhysicalPointSourceResidueAffineBase
            source target)) =
      cmp89SignedLatticeL1ExponentialWeight delta
        (cmp99DiagonalPeriodicDisplacement source target) := by
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  rw [
    cmp89Eq251LatticeL1Length_centered_generatedResidueAffineBase_eq_diagonal]

/-- The arbitrary-residue affine base reaches the existing diagonal owner
metric with no residue-cardinality factor. -/
theorem cmp89SignedLatticeL1ExponentialWeight_centered_generatedResidueAffineBase_le_owner
    {K N : ℕ} [NeZero K] [NeZero N]
    {rho : ℝ} (hrho : 0 ≤ rho)
    (source target : FinBox 4 (K * N)) :
    cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99SourceGeneratedFlatPhysicalPointSourceResidueAffineBase
            source target)) ≤
      Real.exp (2 * rho) *
        Real.exp (-rho *
          (finBoxDist (blockSite K N source) (blockSite K N target) : ℝ)) := by
  rw [
    cmp89SignedLatticeL1ExponentialWeight_centered_generatedResidueAffineBase_eq_diagonal]
  have hcenter :=
    cmp89SignedLatticeL1ExponentialWeight_centeredDiagonal_le_owner
      hrho source target
  calc
    cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
        (cmp99DiagonalPeriodicDisplacement source target) =
      cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99DiagonalPeriodicDisplacement source target)) := by
      rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
        cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
        cmp89Eq251LatticeL1Length_centeredDiagonalPeriodicDisplacement_eq]
    _ ≤ Real.exp (2 * rho) *
        Real.exp (-rho *
          (finBoxDist (blockSite K N source) (blockSite K N target) : ℝ)) :=
      hcenter

end

end YangMills.RG
