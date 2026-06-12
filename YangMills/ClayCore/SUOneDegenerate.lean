/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurZeroMean

/-!
# The boundary case `N_c = 1`: SU(1) is trivial, and what that exposes

Every selection rule in the centre-symmetry programme carries a hypothesis
`N_c ≥ 2` (or `N_c ∤ k`, which fails at `N_c = 1`).  This file explains why, by
**certifying the boundary case as a theorem**:

  `Matrix.specialUnitaryGroup (Fin 1) ℂ` is the **trivial group** `{1}`, and
  consequently `∫ f d(sunHaarProb 1) = f 1` — the Haar "expectation" at `N_c = 1`
  collapses to evaluation at the identity.

Reason: a `1×1` matrix `[a]` is special-unitary iff `det[a] = a = 1`, so the only
element is the identity.  `sunHaarProb 1` is then the Dirac mass at `1`.

## Why this matters beyond bookkeeping

The repository's abelian warm-up `ClayCore/AbelianU1Witness.lean` models the
**U(1)** gauge group as `specialUnitaryGroup (Fin 1) ℂ`.  By the theorem below
that group is *trivial*, so that "U(1) witness" is degenerate: its measure is a
point mass, every Wilson observable is constant, and the correlator it bounds is
identically zero (Leak A of `FOUNDATIONS.md §3`, in its starkest form).  It is not
a model of U(1) at all.

**The correct U(1)** is the circle group `U(1) = Matrix.unitaryGroup (Fin 1) ℂ ≅
Circle ≅ AddCircle 1` — a *non-trivial* compact group.  Mathlib already supports
it with a normalized Haar measure (`AddCircle.haarAddCircle`, a probability
measure) and the Fourier characters (`fourier n`) with their orthonormality
(`orthonormal_fourier`).  That is the substrate on which the genuine U(1)
end-to-end closure of `HORIZON.md §5` should be built — and on which the abelian
analogue of the centre rules becomes the *complete* Fourier orthogonality
`∫ zⁿ dHaar = δ_{n,0}` (the first honestly non-vacuous exact value in reach).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.
(Pending a `lake build` pass.)
-/

namespace YangMills

open MeasureTheory

noncomputable section

/-! ## SU(1) is trivial -/

/-- The only element of `SU(1)` is the identity: a `1×1` special-unitary matrix
has its single entry equal to its determinant, which is `1`. -/
theorem specialUnitaryGroup_fin_one_eq_one
    (U : Matrix.specialUnitaryGroup (Fin 1) ℂ) : U = 1 := by
  have hdet : (U : Matrix (Fin 1) (Fin 1) ℂ).det = 1 := U.2.2
  rw [Matrix.det_fin_one] at hdet
  apply Subtype.ext
  ext i j
  fin_cases i; fin_cases j
  rw [OneMemClass.coe_one, Matrix.one_apply_eq]
  exact hdet

/-- `SU(1)` is a `Subsingleton`. -/
instance : Subsingleton (Matrix.specialUnitaryGroup (Fin 1) ℂ) :=
  ⟨fun a b => by
    rw [specialUnitaryGroup_fin_one_eq_one a, specialUnitaryGroup_fin_one_eq_one b]⟩

/-- `SU(1)` is `Unique` with the identity as its sole element. -/
instance : Unique (Matrix.specialUnitaryGroup (Fin 1) ℂ) where
  default := 1
  uniq U := specialUnitaryGroup_fin_one_eq_one U

/-! ## The Haar expectation at `N_c = 1` is degenerate -/

/-- At `N_c = 1` the Haar integral collapses to evaluation at the identity:
`sunHaarProb 1` is the Dirac mass at `1`.  This makes the degeneracy of any
"U(1)-as-SU(1)" model explicit. -/
theorem sunHaarProb_one_integral_eq
    (f : Matrix.specialUnitaryGroup (Fin 1) ℂ → ℂ) :
    ∫ U, f U ∂(sunHaarProb 1) = f 1 := by
  have huniv : (sunHaarProb 1).real Set.univ = 1 := by simp [measureReal_def]
  rw [integral_unique, huniv, one_smul]
  exact congrArg f (Subsingleton.elim _ _)

/-- In particular the fundamental "character" has nonzero mean at `N_c = 1`
(`∫ tr U = tr 1 = 1`), in stark contrast to `∫ tr U = 0` for `N_c ≥ 2`
(`sunHaarProb_trace_complex_integral_zero`).  The zero-mean phenomenon is genuinely
a `N_c ≥ 2` effect; at `N_c = 1` there is no centre to average over. -/
theorem sunHaarProb_one_trace_integral_eq_one :
    ∫ U : Matrix.specialUnitaryGroup (Fin 1) ℂ,
      U.val.trace ∂(sunHaarProb 1) = 1 := by
  rw [sunHaarProb_one_integral_eq]
  rw [OneMemClass.coe_one, Matrix.trace_one, Fintype.card_fin, Nat.cast_one]

end

end YangMills
