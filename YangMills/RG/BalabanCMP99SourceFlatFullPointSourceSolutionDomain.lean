/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246MassUniformAnalyticDomain
import YangMills.RG.BalabanCMP99SourceFlatQprimeCenteredAliasFibreNonvanishing
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishing

/-!
# Cold-sealed full Eq. (2.46) domains at the two finite-grid representatives

Fresh Colab Pro+ CPU/high-RAM runner
`cmp99-full-point-source-solution-domain-cold-v1` verified exact source
checkpoint `e4f2bbc33599da7b0f7ff91deeb5307719616a25`; see Verification Ledger
Addendum 1088.

The centered and literal uncentered coarse momenta used by the finite-grid
dictionary both satisfy the complete nonvanishing contract of the stabilized
CMP89 (2.46) solver.  At the centered representative the common polistrip
constructs the contract.  At a nonzero physical representative the complete
fine fibre, stabilized denominator and central row are produced separately;
the zero representative is handled directly by the common-polistrip theorem.

This module does not assert a period identity between the two representatives,
identify the centered torus sample with the physical sample, prove CMP89
(2.42), produce `B0` or `delta0`, attain window 15, move `20/41`, or construct
a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The signed centered representative has the complete solver domain used by
the full two-endpoint Green. -/
theorem cmp99SourceFlatFullPointSourceSolutionDomain_centered
    {M N' : ℕ} [NeZero M] [NeZero N'] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (ell : FinBox 4 N') :
    CMP89Eq246FullSolutionDomain 4 M 1 0 a
      (fun mu =>
        (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)) := by
  let p := cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell
  exact cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
    ha.le hrho hamplitude hradius hdenWindow hpairWindow
    (by norm_num [CMP89Eq251UniformMassWindow])
    (p := p)
    (fun mu => abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi ell mu)
    (by intro mu; rfl)
    (by intro mu; simpa using hrho)

/-- The literal uncentered physical representative has the complete solver
domain.  The zero fibre is discharged by the strip constructor; on every
nonzero fibre the three fields are independently derived from the physical
fine-symbol, stabilized-denominator and central-pair producers. -/
theorem cmp99SourceFlatFullPointSourceSolutionDomain_physical
    {M N' : ℕ} [NeZero M] [NeZero N'] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (ell : FinBox 4 N') :
    CMP89Eq246FullSolutionDomain 4 M 1 0 a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) := by
  by_cases hell : ell = 0
  · subst ell
    let p : Fin 4 → ℝ := fun _ => 0
    have hp : ∀ mu, |p mu| ≤ Real.pi := by
      intro mu
      simp [p, Real.pi_pos.le]
    have hreal : ∀ mu,
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
          (0 : FinBox 4 N') mu).re = p mu := by
      intro mu
      simp [p, cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum]
    have himag : ∀ mu,
        |(cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
          (0 : FinBox 4 N') mu).im| ≤ rho := by
      intro mu
      simpa [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum] using hrho
    exact cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
      ha.le hrho hamplitude hradius hdenWindow hpairWindow
      (by norm_num [CMP89Eq251UniformMassWindow]) hp hreal himag
  · refine ⟨?_, ?_, ?_⟩
    · intro m hm
      exact cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
        (d := 4) (M := M) (N' := N') hell m
    · exact cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_physical
        (d := 4) (M := M) (N' := N') ha ell
    · exact cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero 4 M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp89Eq249CentralEntireAveragePair_physicalCoarse_ne_zero ell)

end

end YangMills.RG
