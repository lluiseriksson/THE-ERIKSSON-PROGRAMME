/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq250CentralLaplacianComparison
import YangMills.RG.BalabanCMP89Eq251EntireAverageAmplitude

/-!
# Entire Fourier symbols below CMP89 (2.48)

Compiler verification: source checkpoint
`47a5cb3b626426104ae0f7ef4afd98a2b3aea372`, cold GitHub Actions run
`31242779236` (3277 jobs; focal and eleven-declaration axiom audit exit zero).

CMP89 (2.47)--(2.49) contains the real quantities `|u_j(q)|^2` and
`Delta^xi(q)`.  A holomorphic continuation cannot use complex norm squares.
This module instead constructs the bilinear pairings `u(z) * u(-z)` and
`D_xi(z) * D_xi(-z)`, and identifies their real slices with the already sealed
nonnegative symbols.

No quotient, complex denominator lower bound, uniform analytic strip, contour
displacement, or regional-Green estimate is claimed here.  The flowing
condition `mass^2 <= 1` is not used and is not reclassified as a selectable
smallness window.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Entire continuation of one coordinate of the fine-lattice difference
symbol in CMP89 (2.45). -/
def cmp89Eq245EntireScaledDifference (xi : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (Complex.I * (-((xi : ℂ) * z))) - 1) / (xi : ℂ)

/-- The complex fine-lattice difference is entire in its momentum. -/
@[fun_prop]
theorem differentiable_cmp89Eq245EntireScaledDifference (xi : ℝ) :
    Differentiable ℂ (cmp89Eq245EntireScaledDifference xi) := by
  unfold cmp89Eq245EntireScaledDifference
  fun_prop

/-- Holomorphic continuation of the positive fine-lattice symbol: opposite
momenta replace complex conjugation. -/
def cmp89Eq245EntireScaledLaplacianSymbol
    (d : ℕ) (xi mass : ℝ) (z : Fin d → ℂ) : ℂ :=
  ∑ mu,
      cmp89Eq245EntireScaledDifference xi (z mu) *
        cmp89Eq245EntireScaledDifference xi (-z mu) +
    (mass : ℂ) ^ 2

/-- The holomorphic fine-lattice symbol is entire jointly in all momentum
coordinates. -/
theorem differentiable_cmp89Eq245EntireScaledLaplacianSymbol
    (d : ℕ) (xi mass : ℝ) :
    Differentiable ℂ (cmp89Eq245EntireScaledLaplacianSymbol d xi mass) := by
  unfold cmp89Eq245EntireScaledLaplacianSymbol
  fun_prop

/-- At real momentum, reversing momentum conjugates the entire difference. -/
theorem cmp89Eq245EntireScaledDifference_neg_ofReal_eq_conj
    (xi q : ℝ) :
    cmp89Eq245EntireScaledDifference xi (-(q : ℂ)) =
      starRingEnd ℂ (cmp89Eq245EntireScaledDifference xi (q : ℂ)) := by
  simp [cmp89Eq245EntireScaledDifference, ← Complex.exp_conj]

/-- The entire Laplacian pairing recovers the literal nonnegative symbol on
the real slice. -/
theorem cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq
    (d : ℕ) (xi mass : ℝ) (p : Fin d → ℝ) :
    cmp89Eq245EntireScaledLaplacianSymbol d xi mass
        (fun mu => (p mu : ℂ)) =
      (cmp89Eq245ScaledLaplacianSymbol d xi mass p : ℂ) := by
  rw [cmp89Eq245EntireScaledLaplacianSymbol,
    cmp89Eq245ScaledLaplacianSymbol]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  rw [cmp89Eq245EntireScaledDifference_neg_ofReal_eq_conj,
    Complex.mul_conj']
  rfl

/-- Holomorphic replacement for the real squared averaging amplitude in
CMP89 (2.47)--(2.49). -/
def cmp89Eq245EntireAveragePair
    (d N : ℕ) (z : Fin d → ℂ) : ℂ :=
  cmp89Eq245EntireAverageAmplitude d N z *
    cmp89Eq245EntireAverageAmplitude d N (-z)

/-- The averaging pairing is entire jointly in all momentum coordinates. -/
theorem differentiable_cmp89Eq245EntireAveragePair (d N : ℕ) :
    Differentiable ℂ (cmp89Eq245EntireAveragePair d N) := by
  unfold cmp89Eq245EntireAveragePair
  have havg := differentiable_cmp89Eq245EntireAverageAmplitude d N
  have hneg : Differentiable ℂ (fun z : Fin d → ℂ => -z) := by
    fun_prop
  exact havg.mul (havg.comp hneg)

/-- At real momentum, reversing momentum conjugates the finite geometric
average. -/
theorem cmp89Eq245EntireAverageFactor_neg_ofReal_eq_conj
    (N : ℕ) (q : ℝ) :
    cmp89Eq245EntireAverageFactor N (-(q : ℂ)) =
      starRingEnd ℂ (cmp89Eq245EntireAverageFactor N (q : ℂ)) := by
  simp [cmp89Eq245EntireAverageFactor, cmp89Eq245EntireAverageBase,
    ← Complex.exp_conj]

/-- Product-level reflection identity on the real slice. -/
theorem cmp89Eq245EntireAverageAmplitude_neg_ofReal_eq_conj
    (d N : ℕ) (p : Fin d → ℝ) :
    cmp89Eq245EntireAverageAmplitude d N (fun mu => -(p mu : ℂ)) =
      starRingEnd ℂ
        (cmp89Eq245EntireAverageAmplitude d N (fun mu => (p mu : ℂ))) := by
  rw [cmp89Eq245EntireAverageAmplitude, cmp89Eq245EntireAverageAmplitude,
    map_prod]
  apply Finset.prod_congr rfl
  intro mu _
  exact cmp89Eq245EntireAverageFactor_neg_ofReal_eq_conj N (p mu)

/-- The entire averaging pairing recovers the squared norm of the physical
finite geometric average on the real slice. -/
theorem cmp89Eq245EntireAveragePair_ofReal_eq
    (d N : ℕ) (p : Fin d → ℝ) :
    cmp89Eq245EntireAveragePair d N (fun mu => (p mu : ℂ)) =
      (‖cmp89Eq245EntireAverageAmplitude d N
          (fun mu => (p mu : ℂ))‖ ^ 2 : ℂ) := by
  rw [cmp89Eq245EntireAveragePair]
  change
    cmp89Eq245EntireAverageAmplitude d N (fun mu => (p mu : ℂ)) *
        cmp89Eq245EntireAverageAmplitude d N (fun mu => -(p mu : ℂ)) = _
  rw [cmp89Eq245EntireAverageAmplitude_neg_ofReal_eq_conj,
    Complex.mul_conj']

end

end YangMills.RG
