/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing

/-!
# Neutral mass-zero noncentral physical fine-symbol lemma

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

This generic theorem is currently housed in the diagonal generated-Green
identification module even though its statement and proof are independent of
that endpoint.  Step 8b.24 extracts it to a neutral substrate so both the
diagonal and source-separated identifications can consume it without a
false physical dependency.
-/

namespace YangMills.RG

noncomputable section

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

end

end YangMills.RG
