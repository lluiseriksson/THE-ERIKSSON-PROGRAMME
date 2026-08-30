import YangMills.RG.BalabanCMP89NeumannReflectionResidueDictionary
import YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary

/-!
# CMP89 (2.42): canonical centered rectangular representatives

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this module is compiler-verified.

This module specializes the sealed one-period endpoint dictionary to the
coordinatewise Neumann periods `2 * m_mu`.  The representative and its carry
are constructed internally.  In particular, no caller-selected family of
representatives is accepted.

For the reflected residue `x_mu + n_mu + 1`, the canonical representative has
exactly the printed two-endpoint magnitude

`min (x_mu + n_mu + 1) (2 * m_mu - x_mu - n_mu - 1)`.

The statement is about magnitude: at an even antipodal residue the canonical
signed representative may choose either sign.  This module does not reindex
the full affine fibre, sum reflection branches, assert the Green
representation, construct `B0` or `delta0`, attain window 15, discharge a
terminal field, or instantiate `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Positive natural period corresponding to the literal rectangular period
`2 * m_mu`. -/
def cmp89NeumannReflectionPeriodNat {d : ℕ} (m : Fin d → ℤ)
    (mu : Fin d) : ℕ :=
  (cmp89NeumannReflectionPeriod m mu).natAbs

/-- A positive rectangular side gives a nonzero natural reflection period. -/
theorem cmp89NeumannReflectionPeriodNat_pos {d : ℕ} {m : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu) (mu : Fin d) :
    0 < cmp89NeumannReflectionPeriodNat m mu := by
  rw [cmp89NeumannReflectionPeriodNat, cmp89NeumannReflectionPeriod]
  exact Int.natAbs_pos.mpr (by omega)

/-- Casting the natural period back to the integers recovers the literal
source period.  This equality is exposed before any reindexing. -/
theorem cmp89NeumannReflectionPeriodNat_cast {d : ℕ} {m : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu) (mu : Fin d) :
    (cmp89NeumannReflectionPeriodNat m mu : ℤ) =
      cmp89NeumannReflectionPeriod m mu := by
  rw [cmp89NeumannReflectionPeriodNat, Int.natCast_natAbs]
  exact abs_of_pos (by
    have hmu := hm mu
    rw [cmp89NeumannReflectionPeriod]
    omega)

/-- Canonical centered representative, constructed coordinatewise using the
literal rectangular period. -/
def cmp89NeumannCenteredRectangularRepresentative {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u : Fin d → ℤ) :
    Fin d → ℤ :=
  fun mu =>
    letI : NeZero (cmp89NeumannReflectionPeriodNat m mu) :=
      ⟨Nat.ne_of_gt (cmp89NeumannReflectionPeriodNat_pos hm mu)⟩
    (cmp99CenteredPeriodicEndpointRepresentative
      (cmp89NeumannReflectionPeriodNat m mu) (u mu)).1

/-- Integer carry from the canonical rectangular representative back to the
literal displacement. -/
def cmp89NeumannCenteredRectangularCarry {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u : Fin d → ℤ) :
    Fin d → ℤ :=
  fun mu =>
    letI : NeZero (cmp89NeumannReflectionPeriodNat m mu) :=
      ⟨Nat.ne_of_gt (cmp89NeumannReflectionPeriodNat_pos hm mu)⟩
    cmp99CenteredPeriodicEndpointCarry
      (cmp89NeumannReflectionPeriodNat m mu) (u mu)

/-- Exact coordinatewise reconstruction from the internally constructed
representative and carry. -/
theorem cmp89NeumannCenteredRectangular_reconstruction_apply {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u : Fin d → ℤ)
    (mu : Fin d) :
    u mu = cmp89NeumannCenteredRectangularRepresentative m hm u mu +
      cmp89NeumannReflectionPeriod m mu *
        cmp89NeumannCenteredRectangularCarry m hm u mu := by
  letI : NeZero (cmp89NeumannReflectionPeriodNat m mu) :=
    ⟨Nat.ne_of_gt (cmp89NeumannReflectionPeriodNat_pos hm mu)⟩
  have h :=
    cmp99CenteredPeriodicEndpoint_eq_representative_add_period_mul_carry
      (cmp89NeumannReflectionPeriodNat m mu) (u mu)
  rw [cmp89NeumannReflectionPeriodNat_cast hm mu] at h
  exact h

/-- Vector form of the exact rectangular reconstruction. -/
theorem cmp89NeumannCenteredRectangular_reconstruction {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u : Fin d → ℤ) :
    u = cmp89NeumannCenteredRectangularRepresentative m hm u +
      fun mu => cmp89NeumannReflectionPeriod m mu *
        cmp89NeumannCenteredRectangularCarry m hm u mu := by
  funext mu
  exact cmp89NeumannCenteredRectangular_reconstruction_apply m hm u mu

/-- The canonical rectangular representative is centered in every
coordinate. -/
theorem cmp89NeumannCenteredRectangular_two_natAbs_le {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u : Fin d → ℤ)
    (mu : Fin d) :
    2 * ((cmp89NeumannCenteredRectangularRepresentative m hm u mu).natAbs : ℤ) ≤
      cmp89NeumannReflectionPeriod m mu := by
  letI : NeZero (cmp89NeumannReflectionPeriodNat m mu) :=
    ⟨Nat.ne_of_gt (cmp89NeumannReflectionPeriodNat_pos hm mu)⟩
  have h :=
    cmp99CenteredPeriodicEndpointRepresentative_two_natAbs_le
      (cmp89NeumannReflectionPeriodNat m mu) (u mu)
  rwa [cmp89NeumannReflectionPeriodNat_cast hm mu] at h

/-- For a literal reflected base residue in the half-open source rectangle,
the magnitude of the canonical representative is exactly the two-endpoint
quantity printed by the rectangular reflection geometry. -/
theorem cmp89NeumannCenteredRectangular_reflected_natAbs_eq
    {m x n : ℤ} (hx : 0 ≤ x ∧ x < m) (hn : 0 ≤ n ∧ n < m) :
    let P := (2 * m).natAbs
    letI : NeZero P := ⟨Nat.ne_of_gt (Int.natAbs_pos.mpr (by omega))⟩
    (((cmp99CenteredPeriodicEndpointRepresentative P (x + n + 1)).1).natAbs : ℤ) =
      cmp89NeumannReflectedCenteredMagnitude m x n := by
  dsimp
  let P := (2 * m).natAbs
  let u := x + n + 1
  have hm : 0 < m := by omega
  have hperiod : (P : ℤ) = 2 * m := by
    dsimp [P]
    rw [Int.natCast_natAbs, abs_of_pos (by omega)]
  have hu0 : 0 ≤ u := by omega
  have huP : u < (P : ℤ) := by rw [hperiod]; omega
  have hutoNat : (u.toNat : ℤ) = u := Int.toNat_of_nonneg hu0
  have hutoNat_lt_int : (u.toNat : ℤ) < (P : ℤ) := by
    rw [hutoNat]
    exact huP
  have hutoNat_lt : u.toNat < P := by exact_mod_cast hutoNat_lt_int
  letI : NeZero P := ⟨Nat.ne_of_gt (by exact_mod_cast (show 0 < (P : ℤ) by
    rw [hperiod]
    omega))⟩
  have hmag :=
    cmp99CenteredPeriodicEndpointRepresentative_natAbs_eq_valMinAbs P u
  rw [ZMod.valMinAbs_natAbs_eq_min] at hmag
  have hval : (((u : ℤ) : ZMod P)).val = u.toNat := by
    have hcast : ((u : ℤ) : ZMod P) = (u.toNat : ZMod P) :=
      (congrArg (fun z : ℤ => (z : ZMod P)) hutoNat).symm
    rw [hcast]
    exact ZMod.val_natCast_of_lt hutoNat_lt
  rw [hval] at hmag
  have hsubcast : ((P - u.toNat : ℕ) : ℤ) = 2 * m - u := by
    rw [Nat.cast_sub (Nat.le_of_lt hutoNat_lt), hperiod, hutoNat]
  calc
    (((cmp99CenteredPeriodicEndpointRepresentative P u).1).natAbs : ℤ) =
        (min u.toNat (P - u.toNat) : ℕ) := by exact_mod_cast hmag
    _ = min (u.toNat : ℤ) ((P - u.toNat : ℕ) : ℤ) := by
      simp
    _ = min u (2 * m - u) := by rw [hutoNat, hsubcast]
    _ = cmp89NeumannReflectedCenteredMagnitude m x n := by
      simp only [u, cmp89NeumannReflectedCenteredMagnitude]
      congr 1 <;> ring

/-- The canonical reflected representative retains at least the direct
source-site separation. -/
theorem cmp89Neumann_direct_natAbs_le_centeredReflectedRepresentative
    {m x n : ℤ} (hx : 0 ≤ x ∧ x < m) (hn : 0 ≤ n ∧ n < m) :
    let P := (2 * m).natAbs
    letI : NeZero P := ⟨Nat.ne_of_gt (Int.natAbs_pos.mpr (by omega))⟩
    ((x - n).natAbs : ℤ) ≤
      (((cmp99CenteredPeriodicEndpointRepresentative P (x + n + 1)).1).natAbs : ℤ) := by
  dsimp
  rw [cmp89NeumannCenteredRectangular_reflected_natAbs_eq hx hn]
  exact cmp89Neumann_direct_natAbs_le_reflectedCenteredMagnitude hx hn

end

end YangMills.RG
