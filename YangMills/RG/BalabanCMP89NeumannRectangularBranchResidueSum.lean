import YangMills.RG.BalabanCMP89CenteredRectangularL1ResidueSum
import YangMills.RG.BalabanCMP89NeumannRectangularBranchDistance

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

Exact affine reindexing, varying-period residue estimate and finite
reflection-branch sum for the positive CMP89 Neumann image series.  The final
multiplicity is the literal `2^d`; no rectangle-volume factor is admitted.

This file still does not insert a Green kernel or assert the regional
representation (2.42).
-/

namespace YangMills.RG

noncomputable section

/-- Literal exponential weight of one Neumann reflection image. -/
def cmp89NeumannRectangularBranchImageWeight {d : ℕ}
    (delta : ℝ) (m x n : Fin d → ℤ)
    (branch : CMP89NeumannReflectionBranch d) (k : Fin d → ℤ) : ℝ :=
  cmp89SignedLatticeL1ExponentialWeight delta
    (x - cmp89NeumannReflectionImage m n k branch)

/-- Pointwise form of the exact affine reindexing.  Keeping this equality
separate is what later transports summability before any finite/infinite sums
are exchanged. -/
theorem cmp89NeumannRectangularBranchImageWeight_reindex {d : ℕ}
    (delta : ℝ) (m x n : Fin d → ℤ)
    (hm : ∀ mu, 0 < m mu)
    (branch : CMP89NeumannReflectionBranch d) (k : Fin d → ℤ) :
    cmp89NeumannRectangularBranchImageWeight delta m x n branch k =
      cmp89CenteredRectangularL1ResidueWeight delta
        (cmp89NeumannReflectionPeriodNat m)
        (cmp89NeumannCenteredRectangularRepresentative m hm
          (cmp89NeumannReflectionBaseResidue x n branch))
        (cmp89NeumannCenteredRectangularCarryNegEquiv m hm
          (cmp89NeumannReflectionBaseResidue x n branch) k) := by
  rw [cmp89NeumannRectangularBranchImageWeight,
    cmp89CenteredRectangularL1ResidueWeight_eq_signedLatticeWeight]
  congr 1
  rw [cmp89NeumannReflection_displacement m x n k branch]
  have h := cmp89NeumannRectangular_affine_eq_centered_affine
    m hm (cmp89NeumannReflectionBaseResidue x n branch) k
  convert h using 1
  funext mu
  rw [cmp89NeumannReflectionPeriodNat_cast hm mu]

/-- Absolute summability of one literal image branch, established before the
finite branch sum is interchanged with the integer `tsum`. -/
theorem summable_cmp89NeumannRectangularBranchImageWeight
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {m x n : Fin d → ℤ} (hm : ∀ mu, 0 < m mu)
    (branch : CMP89NeumannReflectionBranch d) :
    Summable (cmp89NeumannRectangularBranchImageWeight
      delta m x n branch) := by
  let u := cmp89NeumannReflectionBaseResidue x n branch
  let e := cmp89NeumannCenteredRectangularCarryNegEquiv m hm u
  apply e.symm.summable_iff.mp
  have hcenter := summable_cmp89CenteredRectangularL1ResidueWeight
    hdelta (cmp89NeumannReflectionPeriodNat_pos hm)
    (cmp89NeumannCenteredRectangularRepresentative m hm u)
  convert hcenter using 1
  funext j
  have hreindex := cmp89NeumannRectangularBranchImageWeight_reindex
    delta m x n hm branch (e.symm j)
  change cmp89NeumannRectangularBranchImageWeight
      delta m x n branch (e.symm j) = _
  rw [hreindex]
  exact congrArg
    (cmp89CenteredRectangularL1ResidueWeight delta
      (cmp89NeumannReflectionPeriodNat m)
      (cmp89NeumannCenteredRectangularRepresentative m hm u))
    (e.apply_symm_apply j)

/-- The literal finite branch sum is summable as a function of the integer
image index.  This is established before any `tsum`/finite-sum exchange. -/
theorem summable_cmp89NeumannRectangularBranchImageWeight_sum
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {m x n : Fin d → ℤ} (hm : ∀ mu, 0 < m mu) :
    Summable (fun k : Fin d → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch d,
        cmp89NeumannRectangularBranchImageWeight
          delta m x n branch k) := by
  exact summable_sum fun branch _ =>
    summable_cmp89NeumannRectangularBranchImageWeight
      hdelta hm branch

/-- Only after branchwise summability is available may the finite branch sum
be exchanged with the integer image `tsum`. -/
theorem tsum_sum_cmp89NeumannRectangularBranchImageWeight_eq_sum_tsum
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {m x n : Fin d → ℤ} (hm : ∀ mu, 0 < m mu) :
    (∑' k : Fin d → ℤ,
        ∑ branch : CMP89NeumannReflectionBranch d,
          cmp89NeumannRectangularBranchImageWeight
            delta m x n branch k) =
      ∑ branch : CMP89NeumannReflectionBranch d,
        ∑' k : Fin d → ℤ,
          cmp89NeumannRectangularBranchImageWeight
            delta m x n branch k := by
  simpa using Summable.tsum_finsetSum
    (s := (Finset.univ : Finset (CMP89NeumannReflectionBranch d)))
    (f := fun branch k =>
      cmp89NeumannRectangularBranchImageWeight delta m x n branch k)
    (fun branch _ =>
      summable_cmp89NeumannRectangularBranchImageWeight hdelta hm branch)

/-- Exact reindexing of one image branch into its internally centered affine
fibre. -/
theorem tsum_cmp89NeumannRectangularBranchImageWeight_eq_centered
    {d : ℕ} (delta : ℝ) (m x n : Fin d → ℤ)
    (hm : ∀ mu, 0 < m mu)
    (branch : CMP89NeumannReflectionBranch d) :
    (∑' k : Fin d → ℤ,
        cmp89NeumannRectangularBranchImageWeight
          delta m x n branch k) =
      ∑' j : Fin d → ℤ,
        cmp89CenteredRectangularL1ResidueWeight delta
          (cmp89NeumannReflectionPeriodNat m)
          (cmp89NeumannCenteredRectangularRepresentative m hm
            (cmp89NeumannReflectionBaseResidue x n branch)) j := by
  let u := cmp89NeumannReflectionBaseResidue x n branch
  let c := cmp89NeumannCenteredRectangularRepresentative m hm u
  calc
    (∑' k : Fin d → ℤ,
        cmp89NeumannRectangularBranchImageWeight
          delta m x n branch k) =
      ∑' k : Fin d → ℤ,
        cmp89SignedLatticeL1ExponentialWeight delta
          (fun mu => u mu + cmp89NeumannReflectionPeriod m mu * (-k mu)) := by
        apply tsum_congr
        intro k
        rw [cmp89NeumannRectangularBranchImageWeight]
        congr 1
        exact cmp89NeumannReflection_displacement m x n k branch
    _ = ∑' j : Fin d → ℤ,
        cmp89SignedLatticeL1ExponentialWeight delta
          (fun mu => c mu + cmp89NeumannReflectionPeriod m mu * j mu) := by
      exact tsum_cmp89NeumannRectangular_eq_centeredAffine
        m hm u (cmp89SignedLatticeL1ExponentialWeight delta)
    _ = ∑' j : Fin d → ℤ,
        cmp89CenteredRectangularL1ResidueWeight delta
          (cmp89NeumannReflectionPeriodNat m) c j := by
      apply tsum_congr
      intro j
      rw [cmp89CenteredRectangularL1ResidueWeight_eq_signedLatticeWeight]
      congr 1
      funext mu
      rw [cmp89NeumannReflectionPeriodNat_cast hm mu]

/-- One reflection branch is bounded by the literal product of geometric
constants times the retained direct `l1` weight. -/
theorem tsum_cmp89NeumannRectangularBranchImageWeight_le
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {m x n : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (branch : CMP89NeumannReflectionBranch d) :
    (∑' k : Fin d → ℤ,
        cmp89NeumannRectangularBranchImageWeight
          delta m x n branch k) ≤
      (∏ mu,
          2 / (1 - Real.exp
            (-delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
        cmp89SignedLatticeL1ExponentialWeight delta (x - n) := by
  rw [tsum_cmp89NeumannRectangularBranchImageWeight_eq_centered
    delta m x n hm branch]
  calc
    (∑' j : Fin d → ℤ,
        cmp89CenteredRectangularL1ResidueWeight delta
          (cmp89NeumannReflectionPeriodNat m)
          (cmp89NeumannCenteredRectangularRepresentative m hm
            (cmp89NeumannReflectionBaseResidue x n branch)) j) ≤
      (∏ mu,
          2 / (1 - Real.exp
            (-delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
        cmp89SignedLatticeL1ExponentialWeight delta
          (cmp89NeumannCenteredRectangularRepresentative m hm
            (cmp89NeumannReflectionBaseResidue x n branch)) := by
      exact tsum_cmp89CenteredRectangularL1ResidueWeight_le
        hdelta (cmp89NeumannReflectionPeriodNat_pos hm)
        (cmp89NeumannCenteredRectangularRepresentative m hm
          (cmp89NeumannReflectionBaseResidue x n branch))
        (cmp89NeumannCenteredRectangular_two_natAbs_le m hm
          (cmp89NeumannReflectionBaseResidue x n branch))
    _ ≤ (∏ mu,
          2 / (1 - Real.exp
            (-delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
        cmp89SignedLatticeL1ExponentialWeight delta (x - n) := by
      apply mul_le_mul_of_nonneg_left
        (cmp89Neumann_centeredBranchWeight_le_directWeight
          hdelta.le hm hx hn branch)
      apply Finset.prod_nonneg
      intro mu _
      have hneg :
          -delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ) < 0 := by
        have hP : 0 < (cmp89NeumannReflectionPeriodNat m mu : ℝ) := by
          exact_mod_cast cmp89NeumannReflectionPeriodNat_pos hm mu
        nlinarith
      exact div_nonneg (by norm_num)
        (sub_nonneg.mpr (le_of_lt (by
          rw [Real.exp_lt_one_iff]
          exact hneg)))

/-- The finite parity sum costs exactly `2^d`, independently of every side
length and of the rectangle volume. -/
theorem sum_tsum_cmp89NeumannRectangularBranchImageWeight_le
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {m x n : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m) :
    (∑ branch : CMP89NeumannReflectionBranch d,
        ∑' k : Fin d → ℤ,
          cmp89NeumannRectangularBranchImageWeight
            delta m x n branch k) ≤
      (2 : ℝ) ^ d *
        ((∏ mu,
            2 / (1 - Real.exp
              (-delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight delta (x - n)) := by
  calc
    (∑ branch : CMP89NeumannReflectionBranch d,
        ∑' k : Fin d → ℤ,
          cmp89NeumannRectangularBranchImageWeight
            delta m x n branch k) ≤
      ∑ _branch : CMP89NeumannReflectionBranch d,
        (∏ mu,
            2 / (1 - Real.exp
              (-delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight delta (x - n) := by
      apply Finset.sum_le_sum
      intro branch _
      exact tsum_cmp89NeumannRectangularBranchImageWeight_le
        hdelta hm hx hn branch
    _ = (2 : ℝ) ^ d *
        ((∏ mu,
            2 / (1 - Real.exp
              (-delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight delta (x - n)) := by
      simp [CMP89NeumannReflectionBranch]

/-- Source-order form of the branch bound: the finite parity sum remains
inside the integer image `tsum`, exactly as in the representation interface.
The preceding summability theorem is the justification for the exchange. -/
theorem tsum_sum_cmp89NeumannRectangularBranchImageWeight_le
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {m x n : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m) :
    (∑' k : Fin d → ℤ,
        ∑ branch : CMP89NeumannReflectionBranch d,
          cmp89NeumannRectangularBranchImageWeight
            delta m x n branch k) ≤
      (2 : ℝ) ^ d *
        ((∏ mu,
            2 / (1 - Real.exp
              (-delta * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight delta (x - n)) := by
  rw [tsum_sum_cmp89NeumannRectangularBranchImageWeight_eq_sum_tsum
    hdelta hm]
  exact sum_tsum_cmp89NeumannRectangularBranchImageWeight_le
    hdelta hm hx hn

end

end YangMills.RG
