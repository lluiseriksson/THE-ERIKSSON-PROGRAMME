import YangMills.RG.BalabanCMP99FlatIntegerResidueClassDictionary
import YangMills.RG.BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary

/-!
# PRE-VALIDATION: physical endpoint carried by an arbitrary residue fibre

The affine residue selected by the two coarse owners must be recombined with
the two within-block endpoint displacements before the centered full-period
weight can be read as the literal fine-site displacement.  The signed
representatives can disagree at an even antipodal seam, so this dictionary
proves equality of the residue and of the exact `l1` length, not equality of
signed vectors.

This draft does not prove CMP89 (2.42), produce uniform physical `B0` or
`delta0`, attain window 15, move `20/41`, or construct a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The affine base left after combining the arbitrary coarse-owner residue
with the two literal within-block endpoint displacements. -/
def cmp99SourceGeneratedFlatPhysicalResidueEndpointBase
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) : Fin d → ℤ :=
  let sourceOwner := blockSite K N source
  let targetOwner := blockSite K N target
  let residue : CMP99FlatZModBox d N :=
    cmp99FinBoxZModEquiv d N sourceOwner -
      cmp99FinBoxZModEquiv d N targetOwner
  fun mu ↦
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        K target targetOwner mu -
      cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        K source sourceOwner mu +
      (K : ℤ) * cmp99FlatIntegerResidueRepresentative residue mu

/-- The combined affine base is the literal `source-target` fine-site
residue modulo the complete physical period `K*N`. -/
theorem cmp99SourceGeneratedFlatPhysicalResidueEndpointBase_cast
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) (mu : Fin d) :
    ((cmp99SourceGeneratedFlatPhysicalResidueEndpointBase
        source target mu : ℤ) : ZMod (K * N)) =
      ((((source mu).val : ℤ) - ((target mu).val : ℤ) : ℤ) :
        ZMod (K * N)) := by
  let sourceOwner := blockSite K N source
  let targetOwner := blockSite K N target
  let residue : CMP99FlatZModBox d N :=
    cmp99FinBoxZModEquiv d N sourceOwner -
      cmp99FinBoxZModEquiv d N targetOwner
  have hresidue :=
    congrFun (cmp99FlatIntegerResidue_representative residue) mu
  have hresidue' :
      ((cmp99FlatIntegerResidueRepresentative residue mu : ℤ) : ZMod N) =
        (((sourceOwner mu).val : ZMod N) -
          ((targetOwner mu).val : ZMod N)) := by
    simpa [residue] using hresidue
  have hdvd : (N : ℤ) ∣
      cmp99FlatIntegerResidueRepresentative residue mu -
        ((sourceOwner mu).val : ℤ) + ((targetOwner mu).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hresidue']
    ring
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases hdvd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  simp only [cmp99SourceGeneratedFlatPhysicalResidueEndpointBase,
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement]
  dsimp only
  push_cast
  change
    ((K : ℤ) * (targetOwner mu).val - (target mu).val -
          ((K : ℤ) * (sourceOwner mu).val - (source mu).val) +
          (K : ℤ) * cmp99FlatIntegerResidueRepresentative residue mu) -
        ((source mu).val - (target mu).val) =
      ((K * N : ℕ) : ℤ) * q
  rw [show
    cmp99FlatIntegerResidueRepresentative residue mu -
          ((sourceOwner mu).val : ℤ) + ((targetOwner mu).val : ℤ) =
        (N : ℤ) * q from hq]
  push_cast
  ring

/-- Centering the combined arbitrary-residue base preserves exactly the
`l1` length of the shortest periodic fine-site displacement. -/
theorem
    cmp89Eq251LatticeL1Length_centered_generatedPhysicalResidueEndpoint_eq
    {d K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox d (K * N)) :
    cmp89Eq251LatticeL1Length
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99SourceGeneratedFlatPhysicalResidueEndpointBase
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
      (cmp99SourceGeneratedFlatPhysicalResidueEndpointBase source target mu)
  change
    (cmp99CenteredPeriodicEndpointRepresentative (K * N)
        (cmp99SourceGeneratedFlatPhysicalResidueEndpointBase
          source target mu)).1.natAbs =
      (cmp99DiagonalPeriodicDisplacement source target mu).natAbs
  rw [hcenter]
  unfold cmp99DiagonalPeriodicDisplacement
    cmp116CMP89PeriodicCoordinateDisplacement
  exact congrArg (fun z : ZMod (K * N) ↦ z.valMinAbs.natAbs)
    (by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        cmp99SourceGeneratedFlatPhysicalResidueEndpointBase_cast
          source target mu)

/-- The centered arbitrary-residue weight is the literal diagonal periodic
fine-site weight. -/
theorem
    cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_eq
    {d K N : ℕ} [NeZero K] [NeZero N]
    (rho : ℝ) (source target : FinBox d (K * N)) :
    cmp89SignedLatticeL1ExponentialWeight rho
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99SourceGeneratedFlatPhysicalResidueEndpointBase
            source target)) =
      cmp89SignedLatticeL1ExponentialWeight rho
        (cmp99DiagonalPeriodicDisplacement source target) := by
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  change
    Real.exp (-rho * cmp89Eq251LatticeL1Length
      (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
        (cmp99SourceGeneratedFlatPhysicalResidueEndpointBase
          source target))) =
      Real.exp (-rho * cmp89Eq251LatticeL1Length
        (cmp99DiagonalPeriodicDisplacement source target))
  rw [cmp89Eq251LatticeL1Length_centered_generatedPhysicalResidueEndpoint_eq]

/-- The arbitrary-residue endpoint therefore inherits the already sealed
diagonal owner bound with no new volume factor. -/
theorem
    cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_le_owner
    {K N : ℕ} [NeZero K] [NeZero N]
    {rho : ℝ} (hrho : 0 ≤ rho)
    (source target : FinBox 4 (K * N)) :
    cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99SourceGeneratedFlatPhysicalResidueEndpointBase
            source target)) ≤
      Real.exp (2 * rho) *
        Real.exp (-rho *
          (finBoxDist (blockSite K N source) (blockSite K N target) : ℝ)) := by
  rw [
    cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_eq]
  exact cmp89SignedLatticeL1ExponentialWeight_centeredDiagonal_le_owner
    hrho source target

end

end YangMills.RG
