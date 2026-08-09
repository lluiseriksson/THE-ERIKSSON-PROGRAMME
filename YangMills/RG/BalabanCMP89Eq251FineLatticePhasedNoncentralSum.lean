/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexNoncentralEndpointQuotientSum
import YangMills.RG.BalabanCMP89Eq251SignedContourPhase

/-!
# Cold-sealed fine-lattice phased noncentral sum below CMP89 (2.49)

Compiler-verified at exact source checkpoint
`db534f72e38422c315cad6bd64d594a7454a9671` by cold GitHub Actions run
`31332625049`. Restoration and saving of `.lake/build` were skipped. The focal
and audit exited zero, and both audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

CMP89 (2.49), printed p. 585, keeps the alias-dependent phase
`exp(i (p' + l) dot u)` inside the reciprocal-alias sum.  For a physical
fine-lattice displacement `u` in `xi Z^4`, these phases cannot be replaced by
one unit-lattice phase.  Their norms on the signed contour are nevertheless
exactly equal because every alias shift `l` is real.

This module inserts each physical phase before summation and proves the same
scale-uniform noncentral majorant, multiplied once by the exact signed
endpoint decay.  It uses the already sealed pointwise quotient estimate and
the same summable source weight; no alias cardinality is introduced.

Honest scope: this is the noncentral replacement for the invalid physical use
of unit-lattice phase factorization.  It does not assemble the central branch,
bound the complete endpoint integrand, identify the Fourier kernel with a
physical Green operator, construct `B0`, attain window 15, discharge a
terminal field or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal noncentral endpoint sum of CMP89 (2.49), retaining the
alias-dependent physical phase inside every summand. -/
def cmp89Eq251ComplexFineLatticePhasedNoncentralSum
    (L j : ℕ) (mass : ℝ) (z : Fin 4 → ℂ) (mu : Fin 4)
    (endpointDisplacement : Fin 4 → ℝ) : ℂ :=
  ∑ m ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
      (cmp89Eq249ZeroAlias 4),
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
      (cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹)
          (-(cmp89Eq248EntireAliasMomentum z m mu)) *
        cmp89Eq245EntireAverageAmplitude 4 (L ^ j)
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m))

/-- Every real reciprocal alias has the same endpoint decay on the signed
contour, so the phase may remain inside the sum without a cardinality loss. -/
theorem norm_cmp89Eq251ComplexFineLatticePhasedNoncentralSum_signedContour_le
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (endpointDisplacement : Fin 4 → ℝ)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq251ComplexFineLatticePhasedNoncentralSum L j mass
        (cmp89Eq251SignedContourMomentum rho p endpointDisplacement) mu
        endpointDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement)) *
        cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho := by
  let N : ℕ := L ^ j
  let aliases := cmp89Eq245CenteredAliasVectors 4 N
  let zeroAlias := cmp89Eq249ZeroAlias 4
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p endpointDisplacement
  let quotient : (Fin 4 → ℤ) → ℂ := fun m =>
    cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹)
        (-(cmp89Eq248EntireAliasMomentum z m mu)) *
      cmp89Eq245EntireAverageAmplitude 4 N
        (cmp89Eq248EntireAliasMomentum z m) /
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m)
  let weight : (Fin 4 → ℤ) → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 0) m
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement))
  have hN : 0 < N :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p endpointDisplacement nu
  have hdecay : 0 ≤ decay :=
    (Real.exp_pos _).le
  have hconstant :
      0 ≤ cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho := by
    rw [cmp89Eq251ComplexNoncentralEndpointQuotientConstant,
      cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpointwise :
      ∀ m ∈ aliases.erase zeroAlias,
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
            quotient m‖ ≤
          decay *
            (cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
              weight m) := by
    intro m hm
    have hmParts := Finset.mem_erase.mp hm
    have hm0 : m ≠ 0 := by
      simpa only [zeroAlias, cmp89Eq249ZeroAlias] using hmParts.1
    have hquotient :=
      norm_cmp89Eq251ComplexNoncentralEndpointQuotient_le_sourceWeight
        (mass := mass) hN hrho hradius hmParts.2 hm0 hp hreal himag
        hamplitude mu
    have hphase :
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement)‖ =
          decay := by
      simpa [z, decay] using
        (norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
          rho p endpointDisplacement m)
    rw [norm_mul, hphase]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [quotient, weight, N, Nat.cast_pow] using hquotient)
      hdecay
  have heraseWeight :
      (∑ m ∈ aliases.erase zeroAlias, weight m) ≤
        ∑ m ∈ aliases, weight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset zeroAlias aliases)
      (fun m _ _ =>
        cmp89Eq251MultidimensionalAliasWeight_nonneg
          (cmp89Eq251AliasSeriesExponent 4 0) m)
  have hseries :
      (∑ m ∈ aliases, weight m) ≤
        (∑' n : ℤ,
          cmp89Eq251OneDimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 0) n) ^ 4 := by
    simpa only [aliases, weight, N] using
      (cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
        (d := 4) N (alpha := (0 : ℝ)) (by norm_num) (by norm_num))
  rw [cmp89Eq251ComplexFineLatticePhasedNoncentralSum,
    cmp89Eq251ComplexNoncentralEndpointQuotientSumBound]
  change ‖∑ m ∈ aliases.erase zeroAlias,
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
        quotient m‖ ≤ _
  calc
    ‖∑ m ∈ aliases.erase zeroAlias,
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
          quotient m‖ ≤
        ∑ m ∈ aliases.erase zeroAlias,
          ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
              (cmp89Eq248EntireAliasMomentum z m) endpointDisplacement) *
            quotient m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ aliases.erase zeroAlias,
        decay *
          (cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
            weight m) := Finset.sum_le_sum hpointwise
    _ = decay *
        (cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
          ∑ m ∈ aliases.erase zeroAlias, weight m) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ decay *
        (cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
          ∑ m ∈ aliases, weight m) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left heraseWeight hconstant) hdecay
    _ ≤ decay *
        (cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
          (∑' n : ℤ,
            cmp89Eq251OneDimensionalAliasWeight
              (cmp89Eq251AliasSeriesExponent 4 0) n) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseries hconstant) hdecay

end

end YangMills.RG
