/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248AliasMomentumCycle
import YangMills.RG.BalabanCMP89Eq245EntireScaledLaplacianPeriodicity
import YangMills.RG.BalabanCMP89MassZeroCentralFineSymbolNonvanishing
import YangMills.RG.BalabanCMP99SourceFlatQprimeCenteredCoarseMomentum

/-!
# PRE-VALIDATION: complete physical alias-fibre nonvanishing at zero mass

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been compiler-verified.

For a nonzero coarse Fourier mode, the signed centered base momentum is
nonzero.  The central alias is therefore covered by the sealed mass-zero
central-symbol theorem, while every other alias is covered by the sealed
noncentral real gap.  This proves nonvanishing on the complete centered
reciprocal fibre.

The literal physical base momentum is not centered.  Its coordinatewise
integer `2*pi` displacement is transported by the already sealed alias-cycle
permutation.  Only the fine symbol, whose pointwise `2*pi*M` period is already
proved, is transported.  No periodicity of the central stabilized denominator
is asserted or used.

Honest scope: this is item 5, gate 4.  It does not prove nonvanishing of the
stabilized denominator, identify the generated Green, attain window 15,
discharge a terminal field, or inhabit `TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The signed centered base momentum is nonzero whenever the coarse mode is
nonzero.  The proof uses the exact residue dictionary; it does not infer this
from interval membership alone. -/
theorem cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_ne_zero
    {d N' : ℕ} [NeZero N'] {ell : FinBox d N'} (hell : ell ≠ 0) :
    cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell ≠ 0 := by
  intro hp
  apply hell
  funext mu
  apply finToZMod_injective
  have hcoord := congrFun hp mu
  rw [cmp99SourceFlatQprimeCenteredCoarseBaseMomentum] at hcoord
  have hN : (N' : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N')
  have haliasReal :
      (cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) = 0 := by
    field_simp [hN] at hcoord
    have hprod :
        (2 * Real.pi) *
            (cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) = 0 := by
      simpa using hcoord
    exact (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
  have halias : cmp99SourceFlatQprimeCenteredCoarseAlias ell mu = 0 := by
    exact_mod_cast haliasReal
  have hresidue :=
    cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg N' (ell mu)
  change
    ((cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℤ) : ZMod N') =
      -(((ell mu).val : ℕ) : ZMod N') at hresidue
  rw [halias] at hresidue
  simpa using hresidue

/-- Nonvanishing of every literal centered alias fine symbol at zero mass and
a nonzero coarse momentum. -/
theorem cmp89Eq245EntireAliasFibre_massZero_ne_zero_centered
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ell : FinBox d N'} (hell : ell ≠ 0) :
    ∀ m : {m : Fin d → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors d M},
      cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) 0
          (cmp89Eq248EntireAliasMomentum
            (fun mu =>
              (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ))
            m.1) ≠ 0 := by
  intro m
  let p := cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell
  have hpCube : ∀ mu, |p mu| ≤ Real.pi :=
    abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi ell
  have hp : p ≠ 0 :=
    cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_ne_zero hell
  by_cases hm0 : m.1 = 0
  · have hcentral :=
      cmp89Eq249CentralEntireFineSymbol_massZero_ne_zero_ofReal
        (N := M) hpCube hp
    simpa [p, cmp89Eq249CentralEntireFineSymbol, hm0,
      cmp89Eq248EntireAliasMomentum_zero] using hcentral
  · have hpos :=
      cmp89Eq245ScaledLaplacianSymbol_noncentral_alias_pos
        (d := d) (N := M) (mass := 0) (m := m.1) (p := p)
        (NeZero.pos M) m.property hm0 hpCube
    let q : Fin d → ℝ :=
      fun mu => p mu + 2 * Real.pi * (m.1 mu : ℝ)
    have halias :
        cmp89Eq248EntireAliasMomentum
            (fun mu => (p mu : ℂ)) m.1 =
          fun mu => (q mu : ℂ) := by
      funext mu
      simp [q, cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift]
    rw [halias, cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)

/-- Complete fine-symbol nonvanishing is periodic under one physical
`2*pi` coordinate shift.  The proof explicitly reindexes the finite alias
fibre; it does not identify corresponding entries without the cycle. -/
theorem cmp89Eq245EntireAliasFibreNonvanishing_physicalShift_iff
    {d M : ℕ} [NeZero M] (mass : ℝ) (mu : Fin d) (z : Fin d → ℂ) :
    (∀ m : {m : Fin d → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors d M},
      cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum
            (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1) ≠ 0) ↔
      ∀ m : {m : Fin d → ℤ //
          m ∈ cmp89Eq245CenteredAliasVectors d M},
        cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m.1) ≠ 0 := by
  let F : (Fin d → ℂ) → ℂ :=
    cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
  have hperiod : ∀ q,
      F (cmp89Eq251CoordinateAliasPeriodShift M mu q) = F q := by
    intro q
    exact
      cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
        (Nat.pos_of_ne_zero (NeZero.ne M)) mass mu q
  let cycle := cmp89Eq245CenteredAliasVectorCycle d M
    (Nat.pos_of_ne_zero (NeZero.ne M)) mu
  have htransport : ∀ m,
      F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1) =
        F (cmp89Eq248EntireAliasMomentum z (cycle m).1) := by
    intro m
    exact cmp89Eq248AliasFactor_physicalShift_eq_cycle
      (Nat.pos_of_ne_zero (NeZero.ne M)) mu z F hperiod m
  constructor
  · intro h m
    have hm := h (cycle.symm m)
    change F (cmp89Eq248EntireAliasMomentum
      (cmp89Eq248PhysicalCoordinatePeriodShift mu z)
        (cycle.symm m).1) ≠ 0 at hm
    rw [htransport (cycle.symm m)] at hm
    change F (cmp89Eq248EntireAliasMomentum z m.1) ≠ 0
    simpa only [Equiv.apply_symm_apply] using hm
  · intro h m
    change F (cmp89Eq248EntireAliasMomentum
      (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1) ≠ 0
    rw [htransport m]
    change F (cmp89Eq248EntireAliasMomentum z (cycle m).1) ≠ 0
    exact h (cycle m)

/-- Coordinatewise integer physical periods preserve complete alias-fibre
nonvanishing.  The integer multiples are accumulated from the one-coordinate
cycle theorem by `Function.Periodic.zsmul`. -/
theorem cmp89Eq245EntireAliasFibreNonvanishing_add_intPeriods_iff
    {d M : ℕ} [NeZero M] (mass : ℝ) (z : Fin d → ℂ)
    (w : Fin d → ℤ) :
    (∀ m : {m : Fin d → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors d M},
      cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum
            (fun mu => z mu + (w mu : ℂ) * (2 * Real.pi : ℂ)) m.1) ≠ 0) ↔
      ∀ m : {m : Fin d → ℤ //
          m ∈ cmp89Eq245CenteredAliasVectors d M},
        cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m.1) ≠ 0 := by
  classical
  let P : (Fin d → ℂ) → Prop := fun q =>
    ∀ m : {m : Fin d → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors d M},
      cmp89Eq245EntireScaledLaplacianSymbol d ((M : ℝ)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum q m.1) ≠ 0
  have hcoordinate : ∀ mu,
      Function.Periodic P (Pi.single mu (2 * Real.pi : ℂ)) := by
    intro mu q
    apply propext
    simpa [P, cmp89Eq248PhysicalCoordinatePeriodShift] using
      (cmp89Eq245EntireAliasFibreNonvanishing_physicalShift_iff
        (d := d) (M := M) mass mu q)
  have hsum : Function.Periodic P
      (∑ mu : Fin d, (w mu) • Pi.single mu (2 * Real.pi : ℂ)) := by
    classical
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simpa [Function.Periodic]
    | @insert mu s hmu ih =>
        rw [Finset.sum_insert hmu]
        exact ((hcoordinate mu).zsmul (w mu)).add_period ih
  have hperiod := hsum z
  have hvector :
      z + (∑ mu : Fin d, (w mu) • Pi.single mu (2 * Real.pi : ℂ)) =
        fun mu => z mu + (w mu : ℂ) * (2 * Real.pi : ℂ) := by
    funext mu
    simp [Pi.single_apply, zsmul_eq_mul]
  rw [hvector] at hperiod
  exact Eq.to_iff hperiod

/-- Consumer-facing form at the literal uncentered physical base momentum:
every depth-one CMP89 alias fine symbol is nonzero at zero mass whenever the
coarse mode is nonzero. -/
theorem cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ell : FinBox d N'} (hell : ell ≠ 0) :
    ∀ m : CMP89Eq246AliasIndex d M 1,
      cmp89Eq246EntireAliasFineSymbol d M 1 0
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) m ≠ 0 := by
  rcases
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods
        ell with
    ⟨w, hw⟩
  have hcentered :=
    cmp89Eq245EntireAliasFibre_massZero_ne_zero_centered
      (d := d) (M := M) (N' := N') hell
  have hunwrapped :=
    (cmp89Eq245EntireAliasFibreNonvanishing_add_intPeriods_iff
      (d := d) (M := M) 0
      (fun mu =>
        (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)) w).2
      hcentered
  intro m
  let m' : {m : Fin d → ℤ //
      m ∈ cmp89Eq245CenteredAliasVectors d M} :=
    ⟨m.1, by
      change m.1 ∈ cmp89Eq245CenteredAliasVectors d (M ^ 1) at m.property
      simpa only [pow_one] using m.property⟩
  have hm := hunwrapped m'
  rw [hw]
  simpa [cmp89Eq246EntireAliasFineSymbol, pow_one, m'] using hm

end

end YangMills.RG
