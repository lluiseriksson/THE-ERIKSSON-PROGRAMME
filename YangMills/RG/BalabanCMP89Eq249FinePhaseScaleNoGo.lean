/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexEndpointAmplitudeFactorization

/-!
# PRE-VALIDATION: fine-lattice phase-scale no-go below CMP89 (2.49)

Source is present at the checkpoint containing this file; its `.olean` has not
yet been materialized and the result is not yet compiler-verified.

CMP89 Lemma 2.4, printed pp. 582 and 584--585, has
`x,x' ∈ L^(-j) Z^d`.  Thus an integer fine-site displacement `u` represents
the physical displacement `xi * u`, where `xi = L^(-j)`.  The reciprocal
aliases in (2.45)--(2.49) are `2*pi*m` in the unscaled physical momentum.

The existing unit-lattice phase lemma is correct for an integer displacement,
but cannot be applied definitionally to the physical fine displacement.  This
module records both the exact scale transport and the smallest counterexample:
at `xi = 1/2`, alias `m = 1` and fine displacement `u = 1`, the alias phase is
`exp(i*pi) = -1`, not one.

Honest scope: this is a no-go for a silent identification of the two phase
conventions.  It does not say that CMP89 (2.49) is false, invalidate the sealed
algebraic endpoint factorization on integer displacements, construct the
correct rescaled Fourier/operator dictionary, produce `B0`, attain window 15,
discharge a terminal field or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- A literal integer fine-site displacement interpreted in the physical
`xi Z^d` coordinates of CMP89 Lemma 2.4. -/
def cmp89Eq249PhysicalFineLatticeDisplacement {d : ℕ}
    (xi : ℝ) (u : Fin d → ℤ) : Fin d → ℝ :=
  fun mu => xi * (u mu : ℝ)

/-- Moving the lattice spacing from the displacement to the momentum is an
exact identity.  It is not the identity obtained by simply dropping `xi`. -/
theorem cmp89Eq251EntirePhase_physicalFineLatticeDisplacement
    {d : ℕ} (xi : ℝ) (z : Fin d → ℂ) (u : Fin d → ℤ) :
    cmp89Eq251EntirePhase z
        (cmp89Eq249PhysicalFineLatticeDisplacement xi u) =
      cmp89Eq251EntirePhase (fun mu => (xi : ℂ) * z mu)
        (cmp89Eq251LatticeDisplacement u) := by
  unfold cmp89Eq251EntirePhase cmp89Eq249PhysicalFineLatticeDisplacement
    cmp89Eq251LatticeDisplacement
  apply Finset.sum_congr rfl
  intro mu _
  push_cast
  ring

/-- The smallest physical fine-scale counterexample to silently reusing the
unit-lattice alias-phase cancellation: one `2*pi` alias across a half-lattice
edge contributes `-1`, not `1`. -/
theorem cmp89Eq249_halfScale_singleAliasPhase_ne_one :
    Complex.exp
        (Complex.I *
          cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum
              (fun _ : Fin 1 => (0 : ℂ)) (fun _ : Fin 1 => (1 : ℤ)))
            (cmp89Eq249PhysicalFineLatticeDisplacement (1 / 2)
              (fun _ : Fin 1 => (1 : ℤ)))) ≠ 1 := by
  rw [show
    Complex.I *
        cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (fun _ : Fin 1 => (0 : ℂ)) (fun _ : Fin 1 => (1 : ℤ)))
          (cmp89Eq249PhysicalFineLatticeDisplacement (1 / 2)
            (fun _ : Fin 1 => (1 : ℤ))) =
      (Real.pi : ℂ) * Complex.I by
    simp [cmp89Eq251EntirePhase, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, cmp89Eq249PhysicalFineLatticeDisplacement]
    ring]
  rw [Complex.exp_pi_mul_I]
  norm_num

end

end YangMills.RG
