import YangMills.RG.BalabanCMP89NeumannCenteredRectangularRepresentative

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

Exact rectangular affine-fibre reindexing for CMP89 (2.42).

The equivalence is the internally constructed carry followed by negation.  No
injectivity hypothesis and no finite-cardinality factor enter.
-/

namespace YangMills.RG

noncomputable section

/-- A direct source displacement already lies in the centered half-period
window.  Hence its internally constructed representative retains exactly the
direct distance; no loss is paid before the reflected branch comparison. -/
theorem cmp89NeumannCenteredRectangular_direct_natAbs_eq
    {m x n : ℤ} (hx : 0 ≤ x ∧ x < m) (hn : 0 ≤ n ∧ n < m) :
    let P := (2 * m).natAbs
    letI : NeZero P := ⟨Nat.ne_of_gt (Int.natAbs_pos.mpr (by omega))⟩
    (((cmp99CenteredPeriodicEndpointRepresentative P (x - n)).1).natAbs : ℤ) =
      ((x - n).natAbs : ℤ) := by
  dsimp
  let P := (2 * m).natAbs
  have hm : 0 < m := by omega
  have hperiod : (P : ℤ) = 2 * m := by
    dsimp [P]
    rw [Int.natCast_natAbs, abs_of_pos (by omega)]
  letI : NeZero P := ⟨Nat.ne_of_gt (by exact_mod_cast
    (show 0 < (P : ℤ) by rw [hperiod]; omega))⟩
  have hval : ((((x - n : ℤ) : ZMod P)).valMinAbs) = x - n := by
    apply (ZMod.valMinAbs_spec (((x - n : ℤ) : ZMod P)) (x - n)).2
    refine ⟨rfl, ?_⟩
    rw [hperiod]
    constructor <;> omega
  rw [cmp99CenteredPeriodicEndpointRepresentative_natAbs_eq_valMinAbs, hval]

/-- The image index `k` is sent to the centered affine index `carry - k`.
This affine reflection is its own inverse. -/
def cmp89NeumannCenteredRectangularCarryNegEquiv {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u : Fin d → ℤ) :
    (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun k := cmp89NeumannCenteredRectangularCarry m hm u - k
  invFun j := cmp89NeumannCenteredRectangularCarry m hm u - j
  left_inv k := by
    funext mu
    simp
  right_inv j := by
    funext mu
    simp

/-- Reindexing by `carry - k` converts the literal rectangular residue fibre
to the canonical centered affine fibre coordinatewise. -/
theorem cmp89NeumannRectangular_affine_eq_centered_affine {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u k : Fin d → ℤ) :
    (fun mu => u mu + cmp89NeumannReflectionPeriod m mu * (-k mu)) =
      (fun mu =>
        cmp89NeumannCenteredRectangularRepresentative m hm u mu +
          cmp89NeumannReflectionPeriod m mu *
            (cmp89NeumannCenteredRectangularCarryNegEquiv m hm u k) mu) := by
  funext mu
  have hrec :=
    cmp89NeumannCenteredRectangular_reconstruction_apply m hm u mu
  change
    u mu + cmp89NeumannReflectionPeriod m mu * (-k mu) =
      cmp89NeumannCenteredRectangularRepresentative m hm u mu +
        cmp89NeumannReflectionPeriod m mu *
          (cmp89NeumannCenteredRectangularCarry m hm u mu - k mu)
  rw [hrec]
  ring

/-- Exact reindexing of an arbitrary rectangular residue-fibre sum. -/
theorem tsum_cmp89NeumannRectangular_eq_centeredAffine {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) (u : Fin d → ℤ)
    (f : (Fin d → ℤ) → ℝ) :
    (∑' k : Fin d → ℤ,
        f (fun mu =>
          u mu + cmp89NeumannReflectionPeriod m mu * (-k mu))) =
      ∑' j : Fin d → ℤ,
        f (fun mu =>
          cmp89NeumannCenteredRectangularRepresentative m hm u mu +
            cmp89NeumannReflectionPeriod m mu * j mu) := by
  let e := cmp89NeumannCenteredRectangularCarryNegEquiv m hm u
  calc
    (∑' k : Fin d → ℤ,
        f (fun mu =>
          u mu + cmp89NeumannReflectionPeriod m mu * (-k mu))) =
      ∑' j : Fin d → ℤ,
        f (fun mu =>
          u mu + cmp89NeumannReflectionPeriod m mu * (-(e.symm j) mu)) := by
        exact e.symm.tsum_eq _ |>.symm
    _ = ∑' j : Fin d → ℤ,
        f (fun mu =>
          cmp89NeumannCenteredRectangularRepresentative m hm u mu +
            cmp89NeumannReflectionPeriod m mu * j mu) := by
      apply tsum_congr
      intro j
      congr 1
      have h := cmp89NeumannRectangular_affine_eq_centered_affine
        m hm u (e.symm j)
      change
        (fun mu =>
          u mu + cmp89NeumannReflectionPeriod m mu * (-(e.symm j) mu)) =
        (fun mu =>
          cmp89NeumannCenteredRectangularRepresentative m hm u mu +
            cmp89NeumannReflectionPeriod m mu * j mu)
      rw [h]
      exact congrArg
        (fun q : Fin d → ℤ =>
          fun mu =>
            cmp89NeumannCenteredRectangularRepresentative m hm u mu +
              cmp89NeumannReflectionPeriod m mu * q mu)
        (e.apply_symm_apply j)

end

end YangMills.RG
