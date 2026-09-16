/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Exact seam-aware residue reindexing for the forward difference of the
source-separated generated flat physical Green.  This file contains only the
finite-torus algebra below D4; it does not assert a derivative estimate,
regional `B0`, window-15 attainment or a terminal field.
-/

-- Promotion imports:
-- import YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary
-- import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointPhase
-- import YangMills.RG.BalabanCMP89Eq248FineLatticeFourierGreenLeftDerivative

namespace YangMills.RG

noncomputable section

/-- Integer carry produced when the positive fine-site shift wraps around the
periodic target box.  It is supported only in the shifted coordinate. -/
def cmp99SourceSeparatedFineTargetShiftCarry
    {d M N : ℕ} (x : FinBox d (M * N)) (mu : Fin d) : Fin d → ℤ :=
  fun nu =>
    if nu = mu ∧ (x mu).val + 1 = M * N then 1 else 0

/-- The raw integer endpoint after a periodic target shift is the ordinary
forward endpoint minus exactly one full fine period when the shift wraps.
This is the point where `FinBox.shift` must not be treated as integer `+1` by
definition. -/
theorem
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement_neg_shift_eq_forward_sub_periodCarry_draft
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N)
    (mu nu : Fin d) :
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          M (x.shift mu) y nu =
      cmp89Eq248FineLatticeForwardCoordinateShift mu
          (fun k =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              M x y k) nu -
        ((M * N : ℕ) : ℤ) *
          cmp99SourceSeparatedFineTargetShiftCarry x mu nu := by
  by_cases hnu : nu = mu
  · subst nu
    by_cases hwrap : (x mu).val + 1 = M * N
    · simp [cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement,
        cmp89Eq248FineLatticeForwardCoordinateShift,
        cmp99SourceSeparatedFineTargetShiftCarry, FinBox.shift, hwrap]
      push_cast
      omega
    · have hlt : (x mu).val + 1 < M * N := by
        omega
      simp [cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement,
        cmp89Eq248FineLatticeForwardCoordinateShift,
        cmp99SourceSeparatedFineTargetShiftCarry, FinBox.shift, hwrap,
        Nat.mod_eq_of_lt hlt]
      push_cast
      ring
  · simp [cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement,
      cmp89Eq248FineLatticeForwardCoordinateShift,
      cmp99SourceSeparatedFineTargetShiftCarry, FinBox.shift, hnu]

/-- Function-valued form of the exact endpoint-shift/carry identity. -/
theorem
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement_neg_shift_eq_forward_sub_periodCarry_fun_draft
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) (mu : Fin d) :
    (fun nu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          M (x.shift mu) y nu) =
      fun nu =>
        cmp89Eq248FineLatticeForwardCoordinateShift mu
            (fun k =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                M x y k) nu -
          ((M * N : ℕ) : ℤ) *
            cmp99SourceSeparatedFineTargetShiftCarry x mu nu := by
  funext nu
  exact
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement_neg_shift_eq_forward_sub_periodCarry_draft
      x y mu nu

/-- Translation of the zero-residue frequency fibre by the target-wrap
carry.  Conjugating `Equiv.addRight` by the exact `Z^d`/zero-residue
equivalence makes preservation of the subtype structural rather than an
assumed congruence. -/
def cmp99SourceSeparatedFineTargetShiftResidueEquiv
    {d M N : ℕ} [NeZero N]
    (x : FinBox d (M * N)) (mu : Fin d) :
    CMP99FlatIntegerResidueClass d N 0 ≃
      CMP99FlatIntegerResidueClass d N 0 :=
  (cmp99FlatIntegerZeroResidueClassEquiv d N).symm.trans
    ((Equiv.addRight
      (cmp99SourceSeparatedFineTargetShiftCarry x mu)).trans
        (cmp99FlatIntegerZeroResidueClassEquiv d N))

/-- The residue equivalence adds exactly `N` times the integer wrap carry in
the underlying frequency representative. -/
theorem cmp99SourceSeparatedFineTargetShiftResidueEquiv_apply_val_draft
    {d M N : ℕ} [NeZero N]
    (x : FinBox d (M * N)) (mu : Fin d)
    (n : CMP99FlatIntegerResidueClass d N 0) (nu : Fin d) :
    (cmp99SourceSeparatedFineTargetShiftResidueEquiv x mu n).1 nu =
      n.1 nu + (N : ℤ) *
        cmp99SourceSeparatedFineTargetShiftCarry x mu nu := by
  change
    (N : ℤ) *
        (cmp99FlatIntegerZeroResidueClassQuotient n nu +
          cmp99SourceSeparatedFineTargetShiftCarry x mu nu) = _
  rw [mul_add,
    cmp99FlatIntegerZeroResidueClassQuotient_spec n nu]

/-- After translating the residue fibre, the wrapped target endpoint is
literally the ordinary forward endpoint in every affine physical residue.
The fine-block factor `M` and coarse-period factor `N` remain separate until
the final ring normalization. -/
theorem
    cmp99SourceSeparatedFineTargetShift_affineResidue_eq_forward_draft
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) (mu : Fin d)
    (n : CMP99FlatIntegerResidueClass d N 0) :
    (fun nu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
            M (x.shift mu) y nu +
          (M : ℤ) *
            (cmp99SourceSeparatedFineTargetShiftResidueEquiv x mu n).1 nu) =
      fun nu =>
        cmp89Eq248FineLatticeForwardCoordinateShift mu
            (fun k =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                M x y k) nu +
          (M : ℤ) * n.1 nu := by
  funext nu
  rw [
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement_neg_shift_eq_forward_sub_periodCarry_draft
      x y mu nu,
    cmp99SourceSeparatedFineTargetShiftResidueEquiv_apply_val_draft]
  push_cast
  ring

/-- Reindex any zero-residue periodization across the target seam.  No
summability hypothesis is needed for a `tsum` change of variables by an
equivalence; summability is needed only in the subsequent subtraction and
termwise divided-difference step. -/
theorem tsum_cmp99SourceSeparatedFineTargetShift_affineResidue_eq_forward_draft
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) (mu : Fin d)
    (f : (Fin d → ℤ) → ℂ) :
    (∑' n : CMP99FlatIntegerResidueClass d N 0,
        f (fun nu =>
          -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              M (x.shift mu) y nu + (M : ℤ) * n.1 nu)) =
      ∑' n : CMP99FlatIntegerResidueClass d N 0,
        f (fun nu =>
          cmp89Eq248FineLatticeForwardCoordinateShift mu
              (fun k =>
                -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                  M x y k) nu + (M : ℤ) * n.1 nu) := by
  let e := cmp99SourceSeparatedFineTargetShiftResidueEquiv x mu
  rw [← e.tsum_eq]
  apply tsum_congr
  intro n
  congr 1
  exact cmp99SourceSeparatedFineTargetShift_affineResidue_eq_forward_draft
    x y mu n

end

end YangMills.RG
