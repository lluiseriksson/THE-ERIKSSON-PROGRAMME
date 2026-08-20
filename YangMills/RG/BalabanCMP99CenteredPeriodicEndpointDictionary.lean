/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This file constructs the centered representative of an arbitrary integer
endpoint displacement modulo the full physical period.  It exposes the
integer carry and the translation equivalence needed to turn the residue-zero
output of Step 8b.22 into the centered periodic sum.  No Green bound, `B0`, or
window-15 attainment is asserted.
-/

import YangMills.RG.BalabanCMP99SourceFlatQprimeSignedAliasMomentumDictionary
import YangMills.RG.BalabanCMP89Eq251ExpandedAliasGeometry
import YangMills.RG.BalabanCMP89CenteredPeriodicL1ResidueSum
import YangMills.RG.BalabanCMP99FlatFiniteGridAliasing

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- The nonnegative quotient chosen so that the signed centered-alias
dictionary represents the residue of `u`, rather than the residue of `-u`. -/
def cmp99CenteredPeriodicEndpointQuotient
    (P : ℕ) [NeZero P] (u : ℤ) : Fin P :=
  (ZMod.finEquiv P).symm (-((u : ℤ) : ZMod P))

/-- Canonical centered representative of an arbitrary integer displacement
modulo the positive period `P`. -/
def cmp99CenteredPeriodicEndpointRepresentative
    (P : ℕ) [NeZero P] (u : ℤ) :
    {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers P} :=
  cmp99SourceFlatQprimeSignedCenteredAliasEquiv P
    (cmp99CenteredPeriodicEndpointQuotient P u)

/-- The canonical centered representative has the same quotient residue as
the original integer displacement. -/
theorem cmp99CenteredPeriodicEndpointRepresentative_cast_eq
    (P : ℕ) [NeZero P] (u : ℤ) :
    (((cmp99CenteredPeriodicEndpointRepresentative P u).1 : ℤ) : ZMod P) =
      ((u : ℤ) : ZMod P) := by
  let q := cmp99CenteredPeriodicEndpointQuotient P u
  have hfin : ((q.1 : ℕ) : ZMod P) = ZMod.finEquiv P q := by
    cases P with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
        rw [show q.1 = (ZMod.finEquiv (n + 1) q).val by rfl]
        exact ZMod.natCast_zmod_val _
  change
    (((cmp99SourceFlatQprimeSignedCenteredAliasEquiv P q).1 : ℤ) : ZMod P) =
      ((u : ℤ) : ZMod P)
  rw [cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg, hfin]
  change
    -(ZMod.finEquiv P
      ((ZMod.finEquiv P).symm (-((u : ℤ) : ZMod P)))) =
        ((u : ℤ) : ZMod P)
  rw [Equiv.apply_symm_apply]
  ring

/-- The difference from the original displacement is an exact multiple of
the full period. -/
theorem cmp99CenteredPeriodicEndpointRepresentative_sub_dvd
    (P : ℕ) [NeZero P] (u : ℤ) :
    (P : ℤ) ∣
      u - (cmp99CenteredPeriodicEndpointRepresentative P u).1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cmp99CenteredPeriodicEndpointRepresentative_cast_eq]
  ring

/-- Integer carry from the centered representative back to the literal
endpoint displacement. -/
def cmp99CenteredPeriodicEndpointCarry
    (P : ℕ) [NeZero P] (u : ℤ) : ℤ :=
  Classical.choose
    (cmp99CenteredPeriodicEndpointRepresentative_sub_dvd P u)

/-- Exact affine decomposition of the endpoint displacement. -/
theorem cmp99CenteredPeriodicEndpoint_eq_representative_add_period_mul_carry
    (P : ℕ) [NeZero P] (u : ℤ) :
    u = (cmp99CenteredPeriodicEndpointRepresentative P u).1 +
      (P : ℤ) * cmp99CenteredPeriodicEndpointCarry P u := by
  have h := Classical.choose_spec
    (cmp99CenteredPeriodicEndpointRepresentative_sub_dvd P u)
  unfold cmp99CenteredPeriodicEndpointCarry
  linarith

/-- Membership in the printed centered interval gives the exact half-period
bound required by the periodic residue sum. -/
theorem cmp99CenteredPeriodicEndpointRepresentative_two_natAbs_le
    (P : ℕ) [NeZero P] (u : ℤ) :
    2 * (((cmp99CenteredPeriodicEndpointRepresentative P u).1).natAbs : ℤ) ≤
      (P : ℤ) := by
  rw [Int.natCast_natAbs]
  exact two_mul_abs_int_le_of_mem_cmp89Eq245CenteredAliasIntegers
    (cmp99CenteredPeriodicEndpointRepresentative P u).property

/-- A centered representative and Mathlib's `valMinAbs` representative of
the same residue have the same magnitude.  At an even antipodal residue they
may have opposite signs, so equality of signed representatives is neither
claimed nor used. -/
theorem natAbs_eq_natAbs_valMinAbs_of_centered
    {P : ℕ} [NeZero P] (m : ℤ)
    (hcenter : 2 * (m.natAbs : ℤ) ≤ (P : ℤ)) :
    m.natAbs = (((m : ℤ) : ZMod P).valMinAbs).natAbs := by
  have hPInt : 0 < (P : ℤ) := by exact_mod_cast NeZero.pos P
  have habs : 2 * |m| ≤ (P : ℤ) := by
    simpa [Int.natCast_natAbs] using hcenter
  have hupper : m * 2 ≤ (P : ℤ) := by
    have hm : m ≤ |m| := le_abs_self m
    nlinarith
  have hlower : -(P : ℤ) ≤ m * 2 := by
    have hm : -m ≤ |m| := neg_le_abs m
    nlinarith
  by_cases hseam : m * 2 = -(P : ℤ)
  · have hcast : ((m : ℤ) : ZMod P) = ((-m : ℤ) : ZMod P) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      have heq : -m - m = (P : ℤ) := by linarith
      rw [heq]
    have hIoc : (-m) * 2 ∈ Set.Ioc (-(P : ℤ)) (P : ℤ) := by
      constructor
      · have heq : (-m) * 2 = (P : ℤ) := by linarith
        rw [heq]
        linarith
      · linarith
    have hval : (((m : ℤ) : ZMod P).valMinAbs) = -m := by
      apply (ZMod.valMinAbs_spec ((m : ℤ) : ZMod P) (-m)).2
      exact ⟨hcast, hIoc⟩
    rw [hval, Int.natAbs_neg]
  · have hIoc : m * 2 ∈ Set.Ioc (-(P : ℤ)) (P : ℤ) := by
      exact ⟨lt_of_le_of_ne hlower (Ne.symm hseam), hupper⟩
    have hval : (((m : ℤ) : ZMod P).valMinAbs) = m := by
      apply (ZMod.valMinAbs_spec ((m : ℤ) : ZMod P) m).2
      exact ⟨rfl, hIoc⟩
    rw [hval]

/-- The CMP89 half-open representative and `valMinAbs` have equal magnitude
for the original endpoint residue, including the even antipodal seam. -/
theorem cmp99CenteredPeriodicEndpointRepresentative_natAbs_eq_valMinAbs
    (P : ℕ) [NeZero P] (u : ℤ) :
    (cmp99CenteredPeriodicEndpointRepresentative P u).1.natAbs =
      (((u : ℤ) : ZMod P).valMinAbs).natAbs := by
  let m := (cmp99CenteredPeriodicEndpointRepresentative P u).1
  have hcenter :=
    cmp99CenteredPeriodicEndpointRepresentative_two_natAbs_le P u
  have hmag := natAbs_eq_natAbs_valMinAbs_of_centered m hcenter
  have hcast := cmp99CenteredPeriodicEndpointRepresentative_cast_eq P u
  change m.natAbs = (((u : ℤ) : ZMod P).valMinAbs).natAbs
  rw [← hcast]
  exact hmag

/-- Coordinatewise centered representative of a physical endpoint vector. -/
def cmp99CenteredPeriodicEndpointVectorRepresentative
    {d : ℕ} (P : ℕ) [NeZero P] (u : Fin d → ℤ) : Fin d → ℤ :=
  fun mu => (cmp99CenteredPeriodicEndpointRepresentative P (u mu)).1

/-- Coordinatewise integer carry. -/
def cmp99CenteredPeriodicEndpointVectorCarry
    {d : ℕ} (P : ℕ) [NeZero P] (u : Fin d → ℤ) : Fin d → ℤ :=
  fun mu => cmp99CenteredPeriodicEndpointCarry P (u mu)

/-- Exact vector affine decomposition. -/
theorem cmp99CenteredPeriodicEndpointVector_eq
    {d : ℕ} (P : ℕ) [NeZero P] (u : Fin d → ℤ) :
    u = cmp99CenteredPeriodicEndpointVectorRepresentative P u +
      fun mu => (P : ℤ) *
        cmp99CenteredPeriodicEndpointVectorCarry P u mu := by
  funext mu
  exact cmp99CenteredPeriodicEndpoint_eq_representative_add_period_mul_carry
    P (u mu)

/-- The vector representative is centered in every coordinate. -/
theorem cmp99CenteredPeriodicEndpointVectorRepresentative_two_natAbs_le
    {d : ℕ} (P : ℕ) [NeZero P] (u : Fin d → ℤ) (mu : Fin d) :
    2 * ((cmp99CenteredPeriodicEndpointVectorRepresentative P u mu).natAbs : ℤ) ≤
      (P : ℤ) :=
  cmp99CenteredPeriodicEndpointRepresentative_two_natAbs_le P (u mu)

/-- Centering a vector already represented coordinatewise by `valMinAbs`
preserves its exact `l1` length.  The statement is deliberately about length,
not signed-vector equality, because the even antipodal seam may flip sign. -/
theorem cmp89Eq251LatticeL1Length_centeredPeriodic_valMinAbs_eq
    {d P : ℕ} [NeZero P] (z : Fin d → ZMod P) :
    cmp89Eq251LatticeL1Length
        (cmp99CenteredPeriodicEndpointVectorRepresentative P
          (fun mu => (z mu).valMinAbs)) =
      cmp89Eq251LatticeL1Length (fun mu => (z mu).valMinAbs) := by
  unfold cmp89Eq251LatticeL1Length
  apply Finset.sum_congr rfl
  intro mu _
  congr 1
  have h :=
    cmp99CenteredPeriodicEndpointRepresentative_natAbs_eq_valMinAbs
      P (z mu).valMinAbs
  simpa using h

/-- Translation of the integer lattice by the carry vector. -/
def cmp99CenteredPeriodicEndpointCarryEquiv
    {d : ℕ} (P : ℕ) [NeZero P] (u : Fin d → ℤ) :
    (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun n := cmp99CenteredPeriodicEndpointVectorCarry P u + n
  invFun n := n - cmp99CenteredPeriodicEndpointVectorCarry P u
  left_inv n := by simp
  right_inv n := by simp

/-- Reindexing by the carry converts the literal residue affine map into the
centered one. -/
theorem cmp99CenteredPeriodicEndpoint_affine_eq_centered_affine
    {d : ℕ} (P : ℕ) [NeZero P] (u n : Fin d → ℤ) :
    (fun mu => u mu + (P : ℤ) * n mu) =
      (fun mu =>
        cmp99CenteredPeriodicEndpointVectorRepresentative P u mu +
          (P : ℤ) *
            (cmp99CenteredPeriodicEndpointCarryEquiv P u n) mu) := by
  funext mu
  have hu := congrFun (cmp99CenteredPeriodicEndpointVector_eq P u) mu
  simp only [Pi.add_apply] at hu ⊢
  change
    u mu + (P : ℤ) * n mu =
      cmp99CenteredPeriodicEndpointVectorRepresentative P u mu +
        (P : ℤ) *
          (cmp99CenteredPeriodicEndpointVectorCarry P u mu + n mu)
  linarith

/-- Exact reindexing of any residue-fibre sum.  This is the bridge consumed
after Step 8b.22 at residue zero; it is not a bound. -/
theorem tsum_cmp99CenteredPeriodicEndpoint_reindex
    {d : ℕ} (P : ℕ) [NeZero P] (u : Fin d → ℤ)
    (f : (Fin d → ℤ) → ℝ) :
    (∑' n : Fin d → ℤ,
        f (fun mu => u mu + (P : ℤ) * n mu)) =
      ∑' n : Fin d → ℤ,
        f (fun mu =>
          cmp99CenteredPeriodicEndpointVectorRepresentative P u mu +
            (P : ℤ) * n mu) := by
  let e := cmp99CenteredPeriodicEndpointCarryEquiv P u
  calc
    (∑' n : Fin d → ℤ,
        f (fun mu => u mu + (P : ℤ) * n mu)) =
      ∑' n : Fin d → ℤ,
        f (fun mu => u mu + (P : ℤ) * (e.symm n) mu) := by
          exact e.symm.tsum_eq _ |>.symm
    _ = ∑' n : Fin d → ℤ,
        f (fun mu =>
          cmp99CenteredPeriodicEndpointVectorRepresentative P u mu +
            (P : ℤ) * n mu) := by
      apply tsum_congr
      intro n
      congr 1
      funext mu
      simp [e, cmp99CenteredPeriodicEndpointCarryEquiv]
      have hu := congrFun (cmp99CenteredPeriodicEndpointVector_eq P u) mu
      simp only [Pi.add_apply] at hu
      linarith

/-- Every coordinate in the zero finite-grid residue class is divisible by
the finite-grid side length. -/
theorem cmp99FlatIntegerZeroResidueClass_coordinate_dvd
    {d N : ℕ} [NeZero N]
    (n : CMP99FlatIntegerResidueClass d N 0) (mu : Fin d) :
    (N : ℤ) ∣ n.1 mu := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := congrFun n.property mu
  simpa [cmp99FlatIntegerResidue] using h

/-- Canonical integer quotient of one coordinate in the zero residue class. -/
def cmp99FlatIntegerZeroResidueClassQuotient
    {d N : ℕ} [NeZero N]
    (n : CMP99FlatIntegerResidueClass d N 0) (mu : Fin d) : ℤ :=
  Classical.choose
    (cmp99FlatIntegerZeroResidueClass_coordinate_dvd n mu)

/-- The quotient reconstructs the literal integer coordinate. -/
theorem cmp99FlatIntegerZeroResidueClassQuotient_spec
    {d N : ℕ} [NeZero N]
    (n : CMP99FlatIntegerResidueClass d N 0) (mu : Fin d) :
    (N : ℤ) * cmp99FlatIntegerZeroResidueClassQuotient n mu = n.1 mu :=
  Classical.choose_spec
    (cmp99FlatIntegerZeroResidueClass_coordinate_dvd n mu)

/-- Exact equivalence between `Z^d` and the residue-zero frequency subtype.
No enumeration or cardinality argument enters. -/
def cmp99FlatIntegerZeroResidueClassEquiv
    (d N : ℕ) [NeZero N] :
    (Fin d → ℤ) ≃ CMP99FlatIntegerResidueClass d N 0 where
  toFun m := ⟨fun mu => (N : ℤ) * m mu, by
    funext mu
    simp [cmp99FlatIntegerResidue]⟩
  invFun n := cmp99FlatIntegerZeroResidueClassQuotient n
  left_inv m := by
    funext mu
    let n : CMP99FlatIntegerResidueClass d N 0 :=
      ⟨fun nu => (N : ℤ) * m nu, by
        funext nu
        simp [cmp99FlatIntegerResidue]⟩
    have h := cmp99FlatIntegerZeroResidueClassQuotient_spec
      n mu
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    change cmp99FlatIntegerZeroResidueClassQuotient n mu = m mu
    change (N : ℤ) * cmp99FlatIntegerZeroResidueClassQuotient n mu =
      (N : ℤ) * m mu at h
    exact mul_left_cancel₀ hN h
  right_inv n := by
    apply Subtype.ext
    funext mu
    exact cmp99FlatIntegerZeroResidueClassQuotient_spec n mu

/-- The residue-zero output of Step 8b.22 is exactly a full-period affine
fibre, then exactly the centered affine fibre.  The first equality uses
`n=N*m`; the second uses the endpoint carry. -/
theorem tsum_cmp99FlatIntegerZeroResidueClass_eq_centeredPeriodic
    {d K N : ℕ} [NeZero K] [NeZero N]
    (u : Fin d → ℤ) (f : (Fin d → ℤ) → ℝ) :
    (∑' n : CMP99FlatIntegerResidueClass d N 0,
        f (fun mu => u mu + (K : ℤ) * n.1 mu)) =
      ∑' m : Fin d → ℤ,
        f (fun mu =>
          cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u mu +
            ((K * N : ℕ) : ℤ) * m mu) := by
  let e := cmp99FlatIntegerZeroResidueClassEquiv d N
  have hKN : NeZero (K * N) :=
    ⟨Nat.mul_ne_zero (NeZero.ne K) (NeZero.ne N)⟩
  letI : NeZero (K * N) := hKN
  calc
    (∑' n : CMP99FlatIntegerResidueClass d N 0,
        f (fun mu => u mu + (K : ℤ) * n.1 mu)) =
      ∑' m : Fin d → ℤ,
        f (fun mu => u mu + ((K * N : ℕ) : ℤ) * m mu) := by
      rw [← e.tsum_eq]
      apply tsum_congr
      intro m
      congr 1
      funext mu
      simp [e, cmp99FlatIntegerZeroResidueClassEquiv]
      push_cast
      ring
    _ = ∑' m : Fin d → ℤ,
        f (fun mu =>
          cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u mu +
            ((K * N : ℕ) : ℤ) * m mu) :=
      tsum_cmp99CenteredPeriodicEndpoint_reindex (K * N) u f

/-- Generic norm bound for the residue-zero output of Step 8b.22.  A literal
fine-lattice coefficient majorant is converted into centered periodic decay,
with no finite-volume factor.  A physical consumer must construct
`hcoefficient` for the actual Green coefficient; this theorem does not accept
or assert the Green identity itself. -/
theorem tsum_norm_cmp99FlatIntegerZeroResidueClass_le_centeredPeriodic
    {d K N : ℕ} [NeZero K] [NeZero N]
    {rho A : ℝ} (hrho : 0 < rho) (hA : 0 ≤ A)
    (coefficient : (Fin d → ℤ) → ℂ)
    (hcoefficient : ∀ v,
      ‖coefficient v‖ ≤ A *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) v)
    (u : Fin d → ℤ) :
    (∑' n : CMP99FlatIntegerResidueClass d N 0,
        ‖coefficient (fun mu => u mu + (K : ℤ) * n.1 mu)‖) ≤
      A *
        ((2 / (1 - Real.exp (-rho))) ^ d *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u)) := by
  have hKN : NeZero (K * N) :=
    ⟨Nat.mul_ne_zero (NeZero.ne K) (NeZero.ne N)⟩
  letI : NeZero (K * N) := hKN
  let uc := cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u
  let weight := cmp89CenteredPeriodicL1ResidueWeight
    (d := d) (rho / (K : ℝ)) (K * N) uc
  have hK : 0 < K := NeZero.pos K
  have hN : 0 < N := NeZero.pos N
  have hKReal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hdelta : 0 < rho / (K : ℝ) := div_pos hrho hKReal
  have hP : 0 < K * N := Nat.mul_pos hK hN
  have hweight : Summable weight :=
    summable_cmp89CenteredPeriodicL1ResidueWeight hdelta hP uc
  have hmajor : Summable (fun m => A * weight m) := hweight.mul_left A
  have hcenter : ∀ mu,
      2 * ((uc mu).natAbs : ℤ) ≤ ((K * N : ℕ) : ℤ) := by
    intro mu
    exact cmp99CenteredPeriodicEndpointVectorRepresentative_two_natAbs_le
      (K * N) u mu
  have hperiodic :=
    tsum_cmp89CenteredPeriodicL1ResidueWeight_physical_uniform_le
      (d := d) hK hN hrho uc hcenter
  rw [tsum_cmp99FlatIntegerZeroResidueClass_eq_centeredPeriodic
    (K := K) (N := N) u (fun v => ‖coefficient v‖)]
  have hleft : Summable (fun m : Fin d → ℤ =>
      ‖coefficient (fun mu => uc mu + ((K * N : ℕ) : ℤ) * m mu)‖) := by
    apply Summable.of_norm_bounded hmajor
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h := hcoefficient
      (fun mu => uc mu + ((K * N : ℕ) : ℤ) * m mu)
    simpa [weight, cmp89CenteredPeriodicL1ResidueWeight,
      cmp89SignedLatticeL1ExponentialWeight] using h
  calc
    (∑' m : Fin d → ℤ,
        ‖coefficient
          (fun mu => uc mu + ((K * N : ℕ) : ℤ) * m mu)‖) ≤
        ∑' m : Fin d → ℤ, A * weight m := by
      apply Summable.tsum_le_tsum _ hleft hmajor
      intro m
      have h := hcoefficient
        (fun mu => uc mu + ((K * N : ℕ) : ℤ) * m mu)
      simpa [weight, cmp89CenteredPeriodicL1ResidueWeight,
        cmp89SignedLatticeL1ExponentialWeight] using h
    _ = A * ∑' m : Fin d → ℤ, weight m := tsum_mul_left
    _ ≤ A *
        ((2 / (1 - Real.exp (-rho))) ^ d *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) uc) :=
      mul_le_mul_of_nonneg_left hperiodic hA
    _ = A *
        ((2 / (1 - Real.exp (-rho))) ^ d *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u)) :=
      rfl

end

end YangMills.RG
