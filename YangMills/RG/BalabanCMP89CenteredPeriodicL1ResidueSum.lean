/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This file isolates the periodic residue estimate needed after Step 8b.22.
Unlike the earlier reverse-triangle majorant, it retains decay in the
centered representative.  No physical Fourier dictionary, `B0`, or
window-15 attainment is asserted.

For `2 * |u| <= P`, the one-dimensional estimate is

  sum_m exp (-delta * |u + P*m|)
    <= 2 / (1 - exp (-delta*P)) * exp (-delta*|u|).

The finite-dimensional product therefore has no volume factor.  At the
physical values `delta = rho/K` and `P = K*N`, its geometric constant is
uniform in `N >= 1`, while the retained decay is
`exp (-(rho/K) * ||u||_1)`.
-/

import YangMills.RG.BalabanCMP89SignedLatticeL1ExponentialSum

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- One coordinate of a periodic residue fibre. -/
def cmp89CenteredPeriodicOneDimensionalExpWeight
    (delta : ℝ) (P : ℕ) (u n : ℤ) : ℝ :=
  Real.exp (-delta * (((u + (P : ℤ) * n).natAbs : ℕ) : ℝ))

/-- The periodic coordinate weight is nonnegative. -/
theorem cmp89CenteredPeriodicOneDimensionalExpWeight_nonneg
    (delta : ℝ) (P : ℕ) (u n : ℤ) :
    0 ≤ cmp89CenteredPeriodicOneDimensionalExpWeight delta P u n := by
  unfold cmp89CenteredPeriodicOneDimensionalExpWeight
  positivity

/-- Reflection of both the representative and the lattice index leaves the
periodic weight unchanged. -/
theorem cmp89CenteredPeriodicOneDimensionalExpWeight_neg_neg
    (delta : ℝ) (P : ℕ) (u n : ℤ) :
    cmp89CenteredPeriodicOneDimensionalExpWeight delta P (-u) (-n) =
      cmp89CenteredPeriodicOneDimensionalExpWeight delta P u n := by
  unfold cmp89CenteredPeriodicOneDimensionalExpWeight
  congr 2
  rw [show -u + (P : ℤ) * -n = -(u + (P : ℤ) * n) by ring]
  norm_cast
  exact Int.natAbs_neg _

/-- On the nonnegative half of a centered residue, the nonnegative lattice
branch is an exact geometric sequence. -/
theorem cmp89CenteredPeriodicOneDimensionalExpWeight_nat_eq
    {delta : ℝ} {P : ℕ} {u : ℤ} (hu : 0 ≤ u) (n : ℕ) :
    cmp89CenteredPeriodicOneDimensionalExpWeight delta P u (n : ℤ) =
      Real.exp (-delta * (u.natAbs : ℝ)) *
        (Real.exp (-delta * (P : ℝ))) ^ n := by
  have hnonneg : 0 ≤ u + (P : ℤ) * (n : ℤ) := by positivity
  have huAbsInt : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu
  have huAbsReal : (u.natAbs : ℝ) = u := by
    rw [← Int.cast_natCast]
    exact congrArg (fun z : ℤ => (z : ℝ)) huAbsInt
  have hsumAbsInt :
      ((u + (P : ℤ) * (n : ℤ)).natAbs : ℤ) =
        u + (P : ℤ) * (n : ℤ) := Int.natAbs_of_nonneg hnonneg
  have hsumAbsReal :
      (((u + (P : ℤ) * (n : ℤ)).natAbs : ℕ) : ℝ) =
        u + (P : ℤ) * (n : ℤ) := by
    calc
      (((u + (P : ℤ) * (n : ℤ)).natAbs : ℕ) : ℝ) =
          (((u + (P : ℤ) * (n : ℤ)).natAbs : ℤ) : ℝ) := by
            rw [Int.cast_natCast]
      _ = ((u + (P : ℤ) * (n : ℤ) : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hsumAbsInt
      _ = (u : ℝ) + (P : ℝ) * (n : ℝ) := by norm_num
  unfold cmp89CenteredPeriodicOneDimensionalExpWeight
  rw [hsumAbsReal, huAbsReal]
  push_cast
  rw [show -delta * ((u : ℝ) + (P : ℝ) * (n : ℝ)) =
      -delta * (u : ℝ) + (-delta * (P : ℝ)) * (n : ℝ) by ring,
    Real.exp_add, mul_comm (-delta * (P : ℝ)) (n : ℝ),
    Real.exp_nat_mul]

/-- On the negative lattice branch, centeredness makes the same geometric
sequence a pointwise majorant.  The inequality `2*u <= P` is the exact place
where the centered representative enters. -/
theorem cmp89CenteredPeriodicOneDimensionalExpWeight_neg_add_one_le
    {delta : ℝ} (hdelta : 0 ≤ delta) {P : ℕ} {u : ℤ}
    (hu : 0 ≤ u) (hcenter : 2 * u ≤ (P : ℤ)) (n : ℕ) :
    cmp89CenteredPeriodicOneDimensionalExpWeight delta P u
        (-((n : ℤ) + 1)) ≤
      Real.exp (-delta * (u.natAbs : ℝ)) *
        (Real.exp (-delta * (P : ℝ))) ^ n := by
  have hnonpos :
      u + (P : ℤ) * (-((n : ℤ) + 1)) ≤ 0 := by
    have hPnonneg : 0 ≤ (P : ℤ) := by positivity
    have hn1 : 1 ≤ (n : ℤ) + 1 := by omega
    have hmul : (P : ℤ) ≤ (P : ℤ) * ((n : ℤ) + 1) := by
      simpa using mul_le_mul_of_nonneg_left hn1 hPnonneg
    have huP : u ≤ (P : ℤ) := by omega
    calc
      u + (P : ℤ) * (-((n : ℤ) + 1)) =
          u - (P : ℤ) * ((n : ℤ) + 1) := by ring
      _ ≤ (P : ℤ) - (P : ℤ) * ((n : ℤ) + 1) := by linarith
      _ ≤ 0 := by linarith
  have habsLower :
      (u.natAbs : ℤ) + (P : ℤ) * (n : ℤ) ≤
        ((u + (P : ℤ) * (-((n : ℤ) + 1))).natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg hu, Int.ofNat_natAbs_of_nonpos hnonpos]
    nlinarith
  have habsLowerReal :
      (u.natAbs : ℝ) + (P : ℝ) * (n : ℝ) ≤
        (((u + (P : ℤ) * (-((n : ℤ) + 1))).natAbs : ℕ) : ℝ) := by
    exact_mod_cast habsLower
  rw [cmp89CenteredPeriodicOneDimensionalExpWeight, ← Real.exp_nat_mul,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A positive period and positive decay make every centered residue fibre
summable. -/
theorem summable_cmp89CenteredPeriodicOneDimensionalExpWeight_of_nonneg
    {delta : ℝ} (hdelta : 0 < delta) {P : ℕ} (hP : 0 < P)
    {u : ℤ} (hu : 0 ≤ u) (hcenter : 2 * u ≤ (P : ℤ)) :
    Summable (cmp89CenteredPeriodicOneDimensionalExpWeight delta P u) := by
  let q : ℝ := Real.exp (-delta * (P : ℝ))
  have hPReal : 0 < (P : ℝ) := by exact_mod_cast hP
  have hqNonneg : 0 ≤ q := (Real.exp_pos _).le
  have hqLt : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hqNonneg hqLt
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (-delta * (u.natAbs : ℝ)) * q ^ n) :=
    hgeom.mul_left _
  apply Summable.of_nat_of_neg_add_one
  · exact hmajor.congr fun n => by
      symm
      simpa [q] using
        cmp89CenteredPeriodicOneDimensionalExpWeight_nat_eq
          (delta := delta) (P := P) hu n
  · apply Summable.of_norm_bounded hmajor
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg
      (cmp89CenteredPeriodicOneDimensionalExpWeight_nonneg
        delta P u (-((n : ℤ) + 1)))]
    simpa [q] using
      cmp89CenteredPeriodicOneDimensionalExpWeight_neg_add_one_le
        hdelta.le hu hcenter n

/-- Summability does not require centeredness; it follows by embedding the
residue fibre injectively in the already sealed full signed lattice. -/
theorem summable_cmp89CenteredPeriodicOneDimensionalExpWeight
    {delta : ℝ} (hdelta : 0 < delta) {P : ℕ} (hP : 0 < P) (u : ℤ) :
    Summable (cmp89CenteredPeriodicOneDimensionalExpWeight delta P u) := by
  have hinj : Function.Injective (fun n : ℤ => u + (P : ℤ) * n) := by
    intro n m hnm
    have hPInt : (P : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
    apply mul_left_cancel₀ hPInt
    linarith
  have hfull := summable_cmp89SignedLatticeOneDimensionalExpWeight hdelta
  exact (hfull.comp_injective hinj).congr fun n => by
    rfl

/-- One-dimensional centered periodic residue bound.  The factor `2` is a
deliberately transparent majorant: one copy for each half of `Int`. -/
theorem tsum_cmp89CenteredPeriodicOneDimensionalExpWeight_le_of_nonneg
    {delta : ℝ} (hdelta : 0 < delta) {P : ℕ} (hP : 0 < P)
    {u : ℤ} (hu : 0 ≤ u) (hcenter : 2 * u ≤ (P : ℤ)) :
    (∑' n : ℤ,
        cmp89CenteredPeriodicOneDimensionalExpWeight delta P u n) ≤
      (2 / (1 - Real.exp (-delta * (P : ℝ)))) *
        Real.exp (-delta * (u.natAbs : ℝ)) := by
  let q : ℝ := Real.exp (-delta * (P : ℝ))
  have hPReal : 0 < (P : ℝ) := by exact_mod_cast hP
  have hqNonneg : 0 ≤ q := (Real.exp_pos _).le
  have hqLt : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hqNonneg hqLt
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (-delta * (u.natAbs : ℝ)) * q ^ n) :=
    hgeom.mul_left _
  have hnat : Summable (fun n : ℕ =>
      cmp89CenteredPeriodicOneDimensionalExpWeight delta P u (n : ℤ)) :=
    hmajor.congr fun n => by
      symm
      simpa [q] using
        cmp89CenteredPeriodicOneDimensionalExpWeight_nat_eq
          (delta := delta) (P := P) hu n
  have hneg : Summable (fun n : ℕ =>
      cmp89CenteredPeriodicOneDimensionalExpWeight delta P u
        (-((n : ℤ) + 1))) := by
    apply Summable.of_norm_bounded hmajor
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg
      (cmp89CenteredPeriodicOneDimensionalExpWeight_nonneg
        delta P u (-((n : ℤ) + 1)))]
    simpa [q] using
      cmp89CenteredPeriodicOneDimensionalExpWeight_neg_add_one_le
        hdelta.le hu hcenter n
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have hnatLe :
      (∑' n : ℕ,
          cmp89CenteredPeriodicOneDimensionalExpWeight delta P u (n : ℤ)) ≤
        ∑' n : ℕ,
          Real.exp (-delta * (u.natAbs : ℝ)) * q ^ n := by
    apply Summable.tsum_le_tsum _ hnat hmajor
    intro n
    exact le_of_eq (by
      simpa [q] using
        cmp89CenteredPeriodicOneDimensionalExpWeight_nat_eq
          (delta := delta) (P := P) hu n)
  have hnegLe :
      (∑' n : ℕ,
          cmp89CenteredPeriodicOneDimensionalExpWeight delta P u
            (-((n : ℤ) + 1))) ≤
        ∑' n : ℕ,
          Real.exp (-delta * (u.natAbs : ℝ)) * q ^ n := by
    apply Summable.tsum_le_tsum _ hneg hmajor
    intro n
    simpa [q] using
      cmp89CenteredPeriodicOneDimensionalExpWeight_neg_add_one_le
        hdelta.le hu hcenter n
  calc
    (∑' n : ℕ,
        cmp89CenteredPeriodicOneDimensionalExpWeight delta P u (n : ℤ)) +
      ∑' n : ℕ,
        cmp89CenteredPeriodicOneDimensionalExpWeight delta P u
          (-((n : ℤ) + 1)) ≤
        2 * (∑' n : ℕ,
          Real.exp (-delta * (u.natAbs : ℝ)) * q ^ n) := by
            linarith
    _ = (2 / (1 - Real.exp (-delta * (P : ℝ)))) *
        Real.exp (-delta * (u.natAbs : ℝ)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hqNonneg hqLt]
      dsimp [q]
      field_simp [ne_of_lt hqLt]

/-- Reflection removes the auxiliary nonnegativity convention from the
one-dimensional estimate. -/
theorem tsum_cmp89CenteredPeriodicOneDimensionalExpWeight_le
    {delta : ℝ} (hdelta : 0 < delta) {P : ℕ} (hP : 0 < P)
    (u : ℤ) (hcenter : 2 * (u.natAbs : ℤ) ≤ (P : ℤ)) :
    (∑' n : ℤ,
        cmp89CenteredPeriodicOneDimensionalExpWeight delta P u n) ≤
      (2 / (1 - Real.exp (-delta * (P : ℝ)))) *
        Real.exp (-delta * (u.natAbs : ℝ)) := by
  by_cases hu : 0 ≤ u
  · exact tsum_cmp89CenteredPeriodicOneDimensionalExpWeight_le_of_nonneg
      hdelta hP hu (by simpa [Int.natAbs_of_nonneg hu] using hcenter)
  · have hneg : 0 ≤ -u := by omega
    have hcenterNeg : 2 * ((-u).natAbs : ℤ) ≤ (P : ℤ) := by
      simpa using hcenter
    calc
      (∑' n : ℤ,
          cmp89CenteredPeriodicOneDimensionalExpWeight delta P u n) =
          ∑' n : ℤ,
            cmp89CenteredPeriodicOneDimensionalExpWeight delta P (-u) n := by
              rw [← (Equiv.neg ℤ).tsum_eq]
              apply tsum_congr
              intro n
              simpa using
                cmp89CenteredPeriodicOneDimensionalExpWeight_neg_neg
                  delta P (-u) n
      _ ≤ (2 / (1 - Real.exp (-delta * (P : ℝ)))) *
          Real.exp (-delta * ((-u).natAbs : ℝ)) :=
        tsum_cmp89CenteredPeriodicOneDimensionalExpWeight_le_of_nonneg
          hdelta hP hneg (by
            have hcenterNeg' := hcenterNeg
            rw [Int.natAbs_of_nonneg hneg] at hcenterNeg'
            exact hcenterNeg')
      _ = (2 / (1 - Real.exp (-delta * (P : ℝ)))) *
          Real.exp (-delta * (u.natAbs : ℝ)) := by simp

/-- Product weight of a periodic residue fibre in `d` coordinates. -/
def cmp89CenteredPeriodicL1ResidueWeight
    {d : ℕ} (delta : ℝ) (P : ℕ)
    (u n : Fin d → ℤ) : ℝ :=
  ∏ mu, cmp89CenteredPeriodicOneDimensionalExpWeight
    delta P (u mu) (n mu)

/-- The product is exactly the signed `l1` exponential weight of `u+P*n`. -/
theorem cmp89CenteredPeriodicL1ResidueWeight_eq_signedLatticeWeight
    {d : ℕ} (delta : ℝ) (P : ℕ) (u n : Fin d → ℤ) :
    cmp89CenteredPeriodicL1ResidueWeight delta P u n =
      cmp89SignedLatticeL1ExponentialWeight delta
        (fun mu => u mu + (P : ℤ) * n mu) := by
  rfl

/-- Summability of a finite product of nonnegative summable integer
families. -/
theorem summable_pi_int_prod_nonneg
    {d : ℕ} (a : Fin d → ℤ → ℝ)
    (ha0 : ∀ mu n, 0 ≤ a mu n)
    (ha : ∀ mu, Summable (a mu)) :
    Summable (fun n : Fin d → ℤ => ∏ mu, a mu (n mu)) := by
  induction d with
  | zero =>
      letI : Finite (Fin 0 → ℤ) :=
        Finite.of_injective (fun _ : Fin 0 → ℤ => PUnit.unit)
          (fun x y _ => Subsingleton.elim x y)
      letI : Fintype (Fin 0 → ℤ) := Fintype.ofFinite _
      exact (hasSum_fintype _).summable
  | succ d hd =>
      let e : ℤ × (Fin d → ℤ) ≃ (Fin (d + 1) → ℤ) :=
        Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)
      let tail : Fin d → ℤ → ℝ := fun mu => a mu.succ
      have hhead : Summable (a 0) := ha 0
      have htail : Summable (fun n : Fin d → ℤ =>
          ∏ mu, tail mu (n mu)) :=
        hd tail (fun mu n => ha0 mu.succ n) (fun mu => ha mu.succ)
      have hpair : Summable (fun p : ℤ × (Fin d → ℤ) =>
          a 0 p.1 * ∏ mu, tail mu (p.2 mu)) :=
        by
          apply (summable_prod_of_nonneg (fun (p : ℤ × (Fin d → ℤ)) => mul_nonneg
            (ha0 0 p.1) (Finset.prod_nonneg fun mu _ =>
              ha0 mu.succ (p.2 mu)))).2
          constructor
          · intro n
            exact htail.mul_left (a 0 n)
          · change Summable (fun n : ℤ =>
              ∑' m : Fin d → ℤ, a 0 n * ∏ mu, tail mu (m mu))
            convert hhead.mul_right (∑' m : Fin d → ℤ,
              ∏ mu, tail mu (m mu)) using 1
            funext n
            rw [htail.tsum_mul_left]
      rw [← e.summable_iff]
      convert hpair using 1
      funext p
      change (∏ mu, a mu ((e p) mu)) =
        a 0 p.1 * ∏ mu, tail mu (p.2 mu)
      rw [Fin.prod_univ_succ]
      rfl

/-- Exact factorization of a nonnegative product family over `Fin d -> Int`.
This helper keeps the product geometry explicit rather than replacing it by
a ball count. -/
theorem tsum_pi_int_prod_nonneg
    {d : ℕ} (a : Fin d → ℤ → ℝ)
    (ha0 : ∀ mu n, 0 ≤ a mu n)
    (ha : ∀ mu, Summable (a mu)) :
    (∑' n : Fin d → ℤ, ∏ mu, a mu (n mu)) =
      ∏ mu, ∑' k : ℤ, a mu k := by
  induction d with
  | zero => simp
  | succ d hd =>
      let e : ℤ × (Fin d → ℤ) ≃ (Fin (d + 1) → ℤ) :=
        Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)
      let tail : Fin d → ℤ → ℝ := fun mu => a mu.succ
      have hhead : Summable (a 0) := ha 0
      have htail : Summable (fun n : Fin d → ℤ =>
          ∏ mu, tail mu (n mu)) :=
        summable_pi_int_prod_nonneg tail
          (fun mu n => ha0 mu.succ n) (fun mu => ha mu.succ)
      have hpair : Summable (fun p : ℤ × (Fin d → ℤ) =>
          a 0 p.1 * ∏ mu, tail mu (p.2 mu)) :=
        by
          apply (summable_prod_of_nonneg (fun (p : ℤ × (Fin d → ℤ)) => mul_nonneg
            (ha0 0 p.1) (Finset.prod_nonneg fun mu _ =>
              ha0 mu.succ (p.2 mu)))).2
          constructor
          · intro n
            exact htail.mul_left (a 0 n)
          · change Summable (fun n : ℤ =>
              ∑' m : Fin d → ℤ, a 0 n * ∏ mu, tail mu (m mu))
            convert hhead.mul_right (∑' m : Fin d → ℤ,
              ∏ mu, tail mu (m mu)) using 1
            funext n
            rw [htail.tsum_mul_left]
      calc
        (∑' n : Fin (d + 1) → ℤ, ∏ mu, a mu (n mu)) =
            ∑' p : ℤ × (Fin d → ℤ),
              a 0 p.1 * ∏ mu, tail mu (p.2 mu) := by
                rw [← e.tsum_eq]
                apply tsum_congr
                intro p
                rw [Fin.prod_univ_succ]
                rfl
        _ = (∑' k : ℤ, a 0 k) *
              (∑' n : Fin d → ℤ, ∏ mu, tail mu (n mu)) := by
                exact (hhead.tsum_mul_tsum htail hpair).symm
        _ = (∑' k : ℤ, a 0 k) *
              ∏ mu, ∑' k : ℤ, tail mu k := by
                rw [hd tail (fun mu n => ha0 mu.succ n)
                  (fun mu => ha mu.succ)]
        _ = ∏ mu, ∑' k : ℤ, a mu k := by
              rw [Fin.prod_univ_succ]

/-- Every positive-decay periodic product fibre is summable. -/
theorem summable_cmp89CenteredPeriodicL1ResidueWeight
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {P : ℕ} (hP : 0 < P) (u : Fin d → ℤ) :
    Summable (cmp89CenteredPeriodicL1ResidueWeight delta P u) := by
  unfold cmp89CenteredPeriodicL1ResidueWeight
  apply summable_pi_int_prod_nonneg
  · intro mu n
    exact cmp89CenteredPeriodicOneDimensionalExpWeight_nonneg
      delta P (u mu) n
  · intro mu
    exact summable_cmp89CenteredPeriodicOneDimensionalExpWeight
      hdelta hP (u mu)

/-- Centered periodic residue bound in `d` dimensions.  The decay in the
centered representative survives, and the only fibre cost is a product of
one-dimensional geometric constants. -/
theorem tsum_cmp89CenteredPeriodicL1ResidueWeight_le
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {P : ℕ} (hP : 0 < P) (u : Fin d → ℤ)
    (hcenter : ∀ mu, 2 * ((u mu).natAbs : ℤ) ≤ (P : ℤ)) :
    (∑' n : Fin d → ℤ,
        cmp89CenteredPeriodicL1ResidueWeight delta P u n) ≤
      (2 / (1 - Real.exp (-delta * (P : ℝ)))) ^ d *
        cmp89SignedLatticeL1ExponentialWeight delta u := by
  let a : Fin d → ℤ → ℝ := fun mu n =>
    cmp89CenteredPeriodicOneDimensionalExpWeight delta P (u mu) n
  have ha0 : ∀ mu n, 0 ≤ a mu n := fun mu n =>
    cmp89CenteredPeriodicOneDimensionalExpWeight_nonneg delta P (u mu) n
  have ha : ∀ mu, Summable (a mu) := by
    intro mu
    exact summable_cmp89CenteredPeriodicOneDimensionalExpWeight
      hdelta hP (u mu)
  change (∑' n : Fin d → ℤ, ∏ mu, a mu (n mu)) ≤ _
  rw [tsum_pi_int_prod_nonneg a ha0 ha]
  calc
    (∏ mu, ∑' k : ℤ, a mu k) ≤
        ∏ mu,
          (2 / (1 - Real.exp (-delta * (P : ℝ)))) *
            Real.exp (-delta * ((u mu).natAbs : ℝ)) := by
      apply Finset.prod_le_prod
      · intro mu _
        exact tsum_nonneg fun n => ha0 mu n
      · intro mu _
        exact tsum_cmp89CenteredPeriodicOneDimensionalExpWeight_le
          hdelta hP (u mu) (hcenter mu)
    _ = (2 / (1 - Real.exp (-delta * (P : ℝ)))) ^ d *
        cmp89SignedLatticeL1ExponentialWeight delta u := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      rw [cmp89SignedLatticeL1ExponentialWeight]
      rfl

/-- Physical specialization.  Here `P = K*N` and `delta = rho/K`, so the
geometric ratio is exactly `exp (-rho*N)` while the retained centered decay
is at the physical fine rate `rho/K`. -/
theorem tsum_cmp89CenteredPeriodicL1ResidueWeight_physical_le
    {d K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    {rho : ℝ} (hrho : 0 < rho) (u : Fin d → ℤ)
    (hcenter : ∀ mu,
      2 * ((u mu).natAbs : ℤ) ≤ ((K * N : ℕ) : ℤ)) :
    (∑' n : Fin d → ℤ,
        cmp89CenteredPeriodicL1ResidueWeight
          (rho / (K : ℝ)) (K * N) u n) ≤
      (2 / (1 - Real.exp (-rho * (N : ℝ)))) ^ d *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) u := by
  have hKReal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hdelta : 0 < rho / (K : ℝ) := div_pos hrho hKReal
  have hP : 0 < K * N := Nat.mul_pos hK hN
  have h := tsum_cmp89CenteredPeriodicL1ResidueWeight_le
    (d := d) hdelta hP u hcenter
  have hscale :
      -(rho / (K : ℝ)) * ((K * N : ℕ) : ℝ) = -rho * (N : ℝ) := by
    push_cast
    field_simp [ne_of_gt hKReal]
  rw [hscale] at h
  exact h

/-- Uniform owner-scale form.  Since `N >= 1`, the geometric constant is
bounded by the `N = 1` constant.  This is the no-volume-factor estimate that
the later physical owner dictionary must consume. -/
theorem tsum_cmp89CenteredPeriodicL1ResidueWeight_physical_uniform_le
    {d K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    {rho : ℝ} (hrho : 0 < rho) (u : Fin d → ℤ)
    (hcenter : ∀ mu,
      2 * ((u mu).natAbs : ℤ) ≤ ((K * N : ℕ) : ℤ)) :
    (∑' n : Fin d → ℤ,
        cmp89CenteredPeriodicL1ResidueWeight
          (rho / (K : ℝ)) (K * N) u n) ≤
      (2 / (1 - Real.exp (-rho))) ^ d *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) u := by
  have hbase := tsum_cmp89CenteredPeriodicL1ResidueWeight_physical_le
    (d := d) hK hN hrho u hcenter
  have hNReal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : Real.exp (-rho * (N : ℝ)) ≤ Real.exp (-rho) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdenPos : 0 < 1 - Real.exp (-rho) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hden :
      1 - Real.exp (-rho) ≤
        1 - Real.exp (-rho * (N : ℝ)) := by linarith
  have hdenMono :
      2 / (1 - Real.exp (-rho * (N : ℝ))) ≤
        2 / (1 - Real.exp (-rho)) := by
    exact div_le_div_of_nonneg_left (by norm_num) hdenPos hden
  have hleftNonneg :
      0 ≤ 2 / (1 - Real.exp (-rho * (N : ℝ))) := by
    exact div_nonneg (by norm_num) (le_trans hdenPos.le hden)
  have hpow := pow_le_pow_left₀ hleftNonneg hdenMono d
  have hweightNonneg :
      0 ≤ cmp89SignedLatticeL1ExponentialWeight
        (rho / (K : ℝ)) u := by
    rw [cmp89SignedLatticeL1ExponentialWeight]
    exact Finset.prod_nonneg fun mu _ =>
      cmp89SignedLatticeOneDimensionalExpWeight_nonneg
        (rho / (K : ℝ)) (u mu)
  exact hbase.trans (mul_le_mul_of_nonneg_right hpow hweightNonneg)

end

end YangMills.RG
