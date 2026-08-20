/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This file is deliberately outside the tracked YangMills tree while the cold
Step 8b.22 verdict is pending.  It isolates the exact infinite-lattice input
needed after the finite selector:

* summability of the literal signed `l1` exponential weight on `Z^d`;
* its exact product/geometric total mass;
* injectivity of a fixed residue-class parametrization `n |-> u + M n`;
* the resulting uniform residue-class bound.

No physical Fourier dictionary, `B0`, or window-15 attainment is asserted.
-/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointRecombination

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- The full signed-lattice product weight is nonnegative. -/
theorem cmp89SignedLatticeL1ExponentialWeight_nonneg
    {d : ℕ} (delta : ℝ) (u : Fin d → ℤ) :
    0 ≤ cmp89SignedLatticeL1ExponentialWeight delta u := by
  rw [cmp89SignedLatticeL1ExponentialWeight]
  exact Finset.prod_nonneg fun mu _ =>
    cmp89SignedLatticeOneDimensionalExpWeight_nonneg delta (u mu)

private theorem cmp89SignedLatticeL1TotalSum_latticeL1Length_neg
    {d : ℕ} (u : Fin d → ℤ) :
    cmp89Eq251LatticeL1Length (fun mu ↦ -u mu) =
      cmp89Eq251LatticeL1Length u := by
  unfold cmp89Eq251LatticeL1Length
  simp

/-- Positive decay makes the literal `l1` product weight summable on all of
`Z^d`.  The induction is through the exact head/tail tuple equivalence; no
ball-counting majorant is introduced. -/
theorem summable_cmp89SignedLatticeL1ExponentialWeight
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta) :
    Summable (cmp89SignedLatticeL1ExponentialWeight (d := d) delta) := by
  induction d with
  | zero =>
      exact Summable.of_finite
  | succ d hd =>
      let e : ℤ × (Fin d → ℤ) ≃ (Fin (d + 1) → ℤ) :=
        Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)
      have hhead :
          Summable (cmp89SignedLatticeOneDimensionalExpWeight delta) :=
        summable_cmp89SignedLatticeOneDimensionalExpWeight hdelta
      have hpair :
          Summable (fun p : ℤ × (Fin d → ℤ) =>
            cmp89SignedLatticeOneDimensionalExpWeight delta p.1 *
              cmp89SignedLatticeL1ExponentialWeight delta p.2) :=
        hhead.mul_of_nonneg hd
          (fun n =>
            cmp89SignedLatticeOneDimensionalExpWeight_nonneg delta n)
          (fun u => cmp89SignedLatticeL1ExponentialWeight_nonneg delta u)
      apply e.summable_iff.mp
      simpa [e, Function.comp_def,
        cmp89SignedLatticeL1ExponentialWeight, Fin.prod_univ_succ] using hpair

/-- Exact total mass of the signed `l1` exponential weight on `Z^d`.
This is the sharp product form matching the norm in which the signed contour
produces decay, so it retains `delta^(-d)` rather than a ball-counting
`delta^(-(d+1))`. -/
theorem tsum_cmp89SignedLatticeL1ExponentialWeight
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta) :
    (∑' u : Fin d → ℤ,
        cmp89SignedLatticeL1ExponentialWeight delta u) =
      ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) ^ d := by
  induction d with
  | zero =>
      rw [tsum_fintype]
      simp [cmp89SignedLatticeL1ExponentialWeight]
  | succ d hd =>
      let e : ℤ × (Fin d → ℤ) ≃ (Fin (d + 1) → ℤ) :=
        Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)
      have hhead :
          Summable (cmp89SignedLatticeOneDimensionalExpWeight delta) :=
        summable_cmp89SignedLatticeOneDimensionalExpWeight hdelta
      have htail :
          Summable
            (cmp89SignedLatticeL1ExponentialWeight (d := d) delta) :=
        summable_cmp89SignedLatticeL1ExponentialWeight hdelta
      have hpair :
          Summable (fun p : ℤ × (Fin d → ℤ) =>
            cmp89SignedLatticeOneDimensionalExpWeight delta p.1 *
              cmp89SignedLatticeL1ExponentialWeight delta p.2) :=
        hhead.mul_of_nonneg htail
          (fun n =>
            cmp89SignedLatticeOneDimensionalExpWeight_nonneg delta n)
          (fun u => cmp89SignedLatticeL1ExponentialWeight_nonneg delta u)
      calc
        (∑' u : Fin (d + 1) → ℤ,
            cmp89SignedLatticeL1ExponentialWeight delta u) =
            ∑' p : ℤ × (Fin d → ℤ),
              cmp89SignedLatticeL1ExponentialWeight delta (e p) := by
                exact (e.tsum_eq
                  (cmp89SignedLatticeL1ExponentialWeight
                    (d := d + 1) delta)).symm
        _ = ∑' p : ℤ × (Fin d → ℤ),
              cmp89SignedLatticeOneDimensionalExpWeight delta p.1 *
                cmp89SignedLatticeL1ExponentialWeight delta p.2 := by
              apply tsum_congr
              intro p
              simp [e, cmp89SignedLatticeL1ExponentialWeight,
                Fin.prod_univ_succ]
        _ = (∑' n : ℤ,
                cmp89SignedLatticeOneDimensionalExpWeight delta n) *
              (∑' u : Fin d → ℤ,
                cmp89SignedLatticeL1ExponentialWeight delta u) := by
              exact (hhead.tsum_mul_tsum htail hpair).symm
        _ = ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) *
              ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) ^ d := by
              rw [tsum_cmp89SignedLatticeOneDimensionalExpWeight hdelta, hd]
        _ = ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) ^ (d + 1) := by
              rw [pow_succ']

/-- Parametrization of the integer lattice points in the residue class `u`
modulo the positive lattice scale `M`. -/
def cmp89SignedLatticeResidueAffineMap
    {d : ℕ} (M : ℕ) (u n : Fin d → ℤ) : Fin d → ℤ :=
  fun mu => u mu + (M : ℤ) * n mu

/-- A positive lattice scale makes each residue-class parametrization
injective. -/
theorem cmp89SignedLatticeResidueAffineMap_injective
    {d M : ℕ} (hM : 0 < M) (u : Fin d → ℤ) :
    Function.Injective (cmp89SignedLatticeResidueAffineMap M u) := by
  intro n m hnm
  funext mu
  have hMInt : (M : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hM
  have hmul : (M : ℤ) * n mu = (M : ℤ) * m mu := by
    simpa [cmp89SignedLatticeResidueAffineMap] using congrFun hnm mu
  exact mul_left_cancel₀ hMInt hmul

/-- Multiplication by the positive integer lattice scale has exactly the
expected effect on literal `l1` length.  Keeping this equality named prevents
the fine/owner conversion from being hidden in later exponential algebra. -/
theorem cmp89Eq251LatticeL1Length_intScale
    {d : ℕ} (M : ℕ) (n : Fin d → ℤ) :
    cmp89Eq251LatticeL1Length (fun mu ↦ (M : ℤ) * n mu) =
      (M : ℝ) * cmp89Eq251LatticeL1Length n := by
  unfold cmp89Eq251LatticeL1Length
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  simp [Int.natAbs_mul]

/-- Reverse triangle inequality in the exact affine-residue convention used
by the physical Fourier coefficient: `M |n|₁ ≤ |u+Mn|₁ + |u|₁`.
This is the scale bookkeeping that avoids replacing the fine rate `rho / M`
by a full-lattice bound at that same rate. -/
theorem cmp89SignedLatticeResidueAffineMap_ownerLength_le
    {d M : ℕ} (u n : Fin d → ℤ) :
    (M : ℝ) * cmp89Eq251LatticeL1Length n ≤
      cmp89Eq251LatticeL1Length
          (cmp89SignedLatticeResidueAffineMap M u n) +
        cmp89Eq251LatticeL1Length u := by
  have htri := cmp89Eq251LatticeL1Length_add_le
    (cmp89SignedLatticeResidueAffineMap M u n) (fun mu ↦ -u mu)
  have hcancel :
      (fun mu ↦
        cmp89SignedLatticeResidueAffineMap M u n mu + -u mu) =
        (fun mu ↦ (M : ℤ) * n mu) := by
    funext mu
    simp [cmp89SignedLatticeResidueAffineMap]
  rw [hcancel, cmp89Eq251LatticeL1Length_intScale,
    cmp89SignedLatticeL1TotalSum_latticeL1Length_neg] at htri
  exact htri

/-- The physical fine-scale residue weight is bounded by the owner-scale
weight with one explicit representative prefactor:

`exp (-(rho/M)|u+Mn|₁) ≤ exp ((rho/M)|u|₁) exp (-rho|n|₁)`.

This is the decisive estimate excluding the spurious `M^d` obtained by
summing the full fine lattice at rate `rho / M`. -/
theorem cmp89SignedLatticeL1ExponentialWeight_physicalResidue_le
    {d M : ℕ} (hM : 0 < M) {rho : ℝ} (hrho : 0 ≤ rho)
    (u n : Fin d → ℤ) :
    cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
        (cmp89SignedLatticeResidueAffineMap M u n) ≤
      Real.exp
          ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u) *
        cmp89SignedLatticeL1ExponentialWeight rho n := by
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hlength :=
    cmp89SignedLatticeResidueAffineMap_ownerLength_le (M := M) u n
  have hscaled :
      rho * cmp89Eq251LatticeL1Length n ≤
        (rho / (M : ℝ)) *
          (cmp89Eq251LatticeL1Length
              (cmp89SignedLatticeResidueAffineMap M u n) +
            cmp89Eq251LatticeL1Length u) := by
    calc
      rho * cmp89Eq251LatticeL1Length n =
          (rho / (M : ℝ)) *
            ((M : ℝ) * cmp89Eq251LatticeL1Length n) := by
              field_simp [ne_of_gt hMReal]
      _ ≤ (rho / (M : ℝ)) *
          (cmp89Eq251LatticeL1Length
              (cmp89SignedLatticeResidueAffineMap M u n) +
            cmp89Eq251LatticeL1Length u) :=
        mul_le_mul_of_nonneg_left hlength (div_nonneg hrho hMReal.le)
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change
    -(rho / (M : ℝ)) *
        cmp89Eq251LatticeL1Length
          (cmp89SignedLatticeResidueAffineMap M u n) ≤
      (rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u +
        -rho * cmp89Eq251LatticeL1Length n
  linarith

/-- Summability of one physical residue fibre at fine rate `rho / M`, with
the majorant already expressed at the owner rate `rho`. -/
theorem summable_cmp89SignedLatticeL1ExponentialWeight_physicalResidue
    {d M : ℕ} (hM : 0 < M) {rho : ℝ} (hrho : 0 < rho)
    (u : Fin d → ℤ) :
    Summable (fun n : Fin d → ℤ ↦
      cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
        (cmp89SignedLatticeResidueAffineMap M u n)) := by
  have hbase :=
    summable_cmp89SignedLatticeL1ExponentialWeight (d := d) hrho
  have hmajor := hbase.mul_left
    (Real.exp ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u))
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (cmp89SignedLatticeL1ExponentialWeight_nonneg
      (rho / (M : ℝ))
      (cmp89SignedLatticeResidueAffineMap M u n))]
  exact cmp89SignedLatticeL1ExponentialWeight_physicalResidue_le
    hM hrho.le u n

/-- Exact owner-scale geometric majorant for a physical residue fibre.  The
only residue dependence is the displayed prefactor; in particular no
`M^d` appears. -/
theorem tsum_cmp89SignedLatticeL1ExponentialWeight_physicalResidue_le
    {d M : ℕ} (hM : 0 < M) {rho : ℝ} (hrho : 0 < rho)
    (u : Fin d → ℤ) :
    (∑' n : Fin d → ℤ,
        cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
          (cmp89SignedLatticeResidueAffineMap M u n)) ≤
      Real.exp
          ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u) *
        ((1 + Real.exp (-rho)) / (1 - Real.exp (-rho))) ^ d := by
  have hleft :=
    summable_cmp89SignedLatticeL1ExponentialWeight_physicalResidue
      hM hrho u
  have hbase :=
    summable_cmp89SignedLatticeL1ExponentialWeight (d := d) hrho
  have hright := hbase.mul_left
    (Real.exp ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u))
  calc
    (∑' n : Fin d → ℤ,
        cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
          (cmp89SignedLatticeResidueAffineMap M u n)) ≤
        ∑' n : Fin d → ℤ,
          Real.exp
              ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u) *
            cmp89SignedLatticeL1ExponentialWeight rho n :=
      Summable.tsum_le_tsum
        (fun n ↦ cmp89SignedLatticeL1ExponentialWeight_physicalResidue_le
          hM hrho.le u n) hleft hright
    _ = Real.exp
          ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u) *
        ((1 + Real.exp (-rho)) / (1 - Real.exp (-rho))) ^ d := by
      rw [tsum_mul_left,
        tsum_cmp89SignedLatticeL1ExponentialWeight hrho]

/-- A centered representative of `l1` length at most `d*M/2` costs at most
the scale-free factor `exp (rho*d/2)`.  In the physical `d = 4` application
this is the advertised `exp (2*rho)`. -/
theorem exp_physicalResidue_prefactor_le_of_centered
    {d M : ℕ} (hM : 0 < M) {rho : ℝ} (hrho : 0 ≤ rho)
    (u : Fin d → ℤ)
    (hcenter : cmp89Eq251LatticeL1Length u ≤
      (d : ℝ) * (M : ℝ) / 2) :
    Real.exp ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u) ≤
      Real.exp (rho * (d : ℝ) / 2) := by
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  apply Real.exp_le_exp.mpr
  calc
    (rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u ≤
        (rho / (M : ℝ)) * ((d : ℝ) * (M : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hcenter (div_nonneg hrho hMReal.le)
    _ = rho * (d : ℝ) / 2 := by
      field_simp [ne_of_gt hMReal]

/-- Four-dimensional form consumed by the Step-8b.23 Fourier coefficient
dictionary.  Once the finite-grid representative is proved centered, the
complete residue fibre has the scale-uniform bound `exp (2*rho)` times the
exact owner-lattice geometric mass. -/
theorem tsum_cmp89SignedLatticeL1ExponentialWeight_physicalResidue_four_le
    {M : ℕ} (hM : 0 < M) {rho : ℝ} (hrho : 0 < rho)
    (u : Fin 4 → ℤ)
    (hcenter : cmp89Eq251LatticeL1Length u ≤ 2 * (M : ℝ)) :
    (∑' n : Fin 4 → ℤ,
        cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
          (cmp89SignedLatticeResidueAffineMap M u n)) ≤
      Real.exp (2 * rho) *
        ((1 + Real.exp (-rho)) / (1 - Real.exp (-rho))) ^ 4 := by
  have hcenter' : cmp89Eq251LatticeL1Length u ≤
      ((4 : ℕ) : ℝ) * (M : ℝ) / 2 := by
    nlinarith [hcenter]
  have hprefactor :
      Real.exp ((rho / (M : ℝ)) * cmp89Eq251LatticeL1Length u) ≤
        Real.exp (2 * rho) := by
    have h := exp_physicalResidue_prefactor_le_of_centered
      (d := 4) hM hrho.le u hcenter'
    convert h using 1
    ring_nf
  have hleft :=
    summable_cmp89SignedLatticeL1ExponentialWeight_physicalResidue
      (d := 4) hM hrho u
  have hbase :=
    summable_cmp89SignedLatticeL1ExponentialWeight (d := 4) hrho
  have hright := hbase.mul_left (Real.exp (2 * rho))
  calc
    (∑' n : Fin 4 → ℤ,
        cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
          (cmp89SignedLatticeResidueAffineMap M u n)) ≤
        ∑' n : Fin 4 → ℤ,
          Real.exp (2 * rho) *
            cmp89SignedLatticeL1ExponentialWeight rho n := by
      apply Summable.tsum_le_tsum _ hleft hright
      intro n
      exact (cmp89SignedLatticeL1ExponentialWeight_physicalResidue_le
        hM hrho.le u n).trans
          (mul_le_mul_of_nonneg_right hprefactor
            (cmp89SignedLatticeL1ExponentialWeight_nonneg rho n))
    _ = Real.exp (2 * rho) *
        ((1 + Real.exp (-rho)) / (1 - Real.exp (-rho))) ^ 4 := by
      rw [tsum_mul_left,
        tsum_cmp89SignedLatticeL1ExponentialWeight hrho]

/-- Every fixed residue class has total signed-`l1` weight bounded by the
full lattice mass, uniformly in the residue representative.  This is a pure
lattice estimate; the physical Fourier-to-residue dictionary remains a
separate obligation. -/
theorem tsum_cmp89SignedLatticeL1ExponentialWeight_residue_le_geometric_pow
    {d M : ℕ} (hM : 0 < M) (u : Fin d → ℤ)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑' n : Fin d → ℤ,
        cmp89SignedLatticeL1ExponentialWeight delta
          (cmp89SignedLatticeResidueAffineMap M u n)) ≤
      ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) ^ d := by
  have hsummable :
      Summable
        (cmp89SignedLatticeL1ExponentialWeight (d := d) delta) :=
    summable_cmp89SignedLatticeL1ExponentialWeight hdelta
  calc
    (∑' n : Fin d → ℤ,
        cmp89SignedLatticeL1ExponentialWeight delta
          (cmp89SignedLatticeResidueAffineMap M u n)) ≤
        ∑' z : Fin d → ℤ,
          cmp89SignedLatticeL1ExponentialWeight delta z := by
            simpa [Function.comp_def] using
              tsum_comp_le_tsum_of_inj hsummable
                (fun z =>
                  cmp89SignedLatticeL1ExponentialWeight_nonneg delta z)
                (cmp89SignedLatticeResidueAffineMap_injective hM u)
    _ = ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) ^ d :=
      tsum_cmp89SignedLatticeL1ExponentialWeight hdelta

end

end YangMills.RG
