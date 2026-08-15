/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalAmbientPrecisionComplexDictionary
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing

/-!
# Generated flat physical Green identification

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its result has not yet been verified by the compiler.

The internally generated ambient Green is transported through the exact
Step-7b carrier equivalence, retaining the physical factorization with block
side `M^(depth+1)` and coarse side `2*(M*Q)`.  Its left-inverse law follows
from the sealed ambient inverse and the sealed physical precision dictionary.

The two scalar nonvanishing families consumed by inverse uniqueness are
constructed internally at zero mass.  A nonzero coarse mode uses complete
physical alias-fibre nonvanishing.  At the zero coarse mode, exclusion of the
physical central alias is transported to exclusion of the zero signed alias,
where the sealed noncentral real gap applies.  The stabilized central
denominator is the literal generated Gate-5 theorem.

The endpoint therefore identifies the literal stabilized Step-7b field with
the generated Green applied to the literal coefficient-one `Q'^*`, without a
caller-supplied inverse, precision dictionary, or scalar nonvanishing family.
It does not prove a regional Green bound, attain window 15, discharge a
terminal field, or inhabit `TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- The internally generated ambient Green in the exact Step-7b full-box
coordinates.  The coordinate equivalence, not arithmetic equality of total
side lengths, fixes the physical factorization. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
    (hM : 2 ≤ M) (depth : ℕ) :
    (FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) →
        SUNLieComplexCoord Nc) →L[ℂ]
      (FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) →
        SUNLieComplexCoord Nc) :=
  let U := cmp99SourceGeneratedPhysicalStep7bFieldEquiv M Q Nc depth
  U.toContinuousLinearMap.comp
    ((cmp99SourceGeneratedFlatPhysicalAmbientGreenComplex
      (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        U.symm.toContinuousLinearMap)

/-- The generated Step-7b Green is a literal left inverse of the literal
full-box Step-7b precision. -/
theorem cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM_comp_precision
    (hM : 2 ≤ M) (depth : ℕ) :
    (cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
      (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        (cmp99SourceFlatFullComplexPrecisionCLM
          (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
          (Nc := Nc) 0
          (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)) =
      ContinuousLinearMap.id ℂ
        (FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) →
          SUNLieComplexCoord Nc) := by
  let U := cmp99SourceGeneratedPhysicalStep7bFieldEquiv M Q Nc depth
  let K := cmp99SourceFlatFullComplexPrecisionCLM
    (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
    (Nc := Nc) 0
    (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
  let A := cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex
    (M := M) (Q := Q) (Nc := Nc) hM depth
  let G := cmp99SourceGeneratedFlatPhysicalAmbientGreenComplex
    (M := M) (Q := Q) (Nc := Nc) hM depth
  have hdict : A =
      cmp99SourceGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
        (M := M) (Q := Q) (Nc := Nc) depth :=
    cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex_eq_step7b
      (M := M) (Q := Q) (Nc := Nc) hM depth
  have hGA : G.comp A = ContinuousLinearMap.id ℂ _ :=
    cmp99SourceGeneratedFlatPhysicalAmbientGreenComplex_comp_precision
      (M := M) (Q := Q) (Nc := Nc) hM depth
  apply ContinuousLinearMap.ext
  intro z
  have hdictz : A (U.symm z) = U.symm (K z) := by
    have h := congrArg (fun T => T (U.symm z)) hdict
    simpa [cmp99SourceGeneratedFlatPhysicalStep7bAmbientPrecisionCLM,
      U, K] using h
  have hGAz : G (A (U.symm z)) = U.symm z := by
    have h := congrArg (fun T => T (U.symm z)) hGA
    simpa [G, A] using h
  change U (G (U.symm (K z))) = z
  rw [← hdictz, hGAz]
  exact U.apply_symm_apply z

/-- At zero mass, every noncentral entry of every literal physical
fixed-coarse fibre has nonzero fine symbol.  The zero coarse mode is handled
separately rather than borrowed from the nonzero-coarse theorem. -/
theorem cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (hk : k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
      (d := d) (M := M) (N' := N') ell) :
    cmp99SourceFlatQprimePhysicalFineSymbol 0 k.1 ≠ 0 := by
  rw [cmp99SourceFlatQprimePhysicalFineSymbol_eq_entireAliasFineSymbol
    (d := d) (M := M) (N' := N') ell 0 k]
  by_cases hell : ell = 0
  · subst ell
    let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
      d M N' (0 : FinBox d N')
    let m := e k
    have hmCentral : m ≠ cmp89Eq249CentralAliasIndex d M 1 := by
      intro hm
      apply hk
      apply e.injective
      rw [cmp99SourceFlatQprimePhysicalCentralAliasIndex_reindex]
      exact hm
    have hm0 : m.1 ≠ 0 := by
      intro hm
      apply hmCentral
      apply Subtype.ext
      simpa [cmp89Eq249CentralAliasIndex, cmp89Eq249ZeroAlias] using hm
    have hmMemPow :
        m.1 ∈ cmp89Eq245CenteredAliasVectors d (M ^ 1) := by
      change m.1 ∈ cmp89Eq245CenteredAliasVectors d (M ^ 1)
      exact m.property
    have hmMem :
        m.1 ∈ cmp89Eq245CenteredAliasVectors d M := by
      simpa only [pow_one] using hmMemPow
    let p : Fin d → ℝ := fun _ => 0
    have hpCube : ∀ mu, |p mu| ≤ Real.pi := by
      intro mu
      simp [p, Real.pi_pos.le]
    have hpos :=
      cmp89Eq245ScaledLaplacianSymbol_noncentral_alias_pos
        (d := d) (N := M) (mass := 0) (m := m.1) (p := p)
        (NeZero.pos M) hmMem hm0 hpCube
    let q : Fin d → ℝ :=
      fun mu => p mu + 2 * Real.pi * (m.1 mu : ℝ)
    have hbase :
        cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (0 : FinBox d N') = fun _ => 0 := by
      funext mu
      simp [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum]
    have halias :
        cmp89Eq248EntireAliasMomentum
            (fun mu =>
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                (0 : FinBox d N') mu : ℂ)) m.1 =
          fun mu => (q mu : ℂ) := by
      rw [hbase]
      funext mu
      simp [q, p, cmp89Eq248EntireAliasMomentum,
        cmp89Eq245AliasShift]
    change cmp89Eq246EntireAliasFineSymbol d M 1 0
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
        (0 : FinBox d N')) m ≠ 0
    rw [cmp89Eq246EntireAliasFineSymbol, halias,
      cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq]
    simpa only [pow_one] using
      Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  · exact cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
      (d := d) (M := M) (N' := N') hell
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
        d M N' ell k)

/-- Generated physical endpoint: the literal stabilized Step-7b field is the
internally generated Green applied to the literal coefficient-one `Q'^*`.
All scalar nonvanishing and inverse data are constructed in the proof. -/
theorem cmp99SourceGeneratedFlatPhysicalStabilizedFieldCLM_eq_green_comp
    (hM : 2 ≤ M) (depth : ℕ) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
        (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
        (Nc := Nc) 0
        (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0) =
      (cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
        (M := M) (Q := Q) (Nc := Nc) hM depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
          (Nc := Nc)) := by
  apply cmp99SourceFlatFullComplexPrecisionStabilizedFieldCLM_eq_inverse_comp
    (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
    (Nc := Nc)
  · exact cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM_comp_precision
      (M := M) (Q := Q) (Nc := Nc) hM depth
  · intro ell k hk
    exact cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral
      ell k hk
  · exact cmp99SourceGeneratedFlatPhysicalStabilizedAliasDenominator_ne_zero
      M Q depth

end

end YangMills.RG
