/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246StabilizedAliasFullSolution
import YangMills.RG.BalabanCMP89Eq249FinePhaseScaleNoGo
import YangMills.RG.BalabanCMP89Eq249CentralAveragePairComplexNonzero
import YangMills.RG.BalabanCMP89Eq251CommonStripHolomorphy

/-!
# PRE-VALIDATION: fine-point-source specialization of CMP89 (2.46)

CMP89 (2.43) uses the Fourier convention

`f_tilde(p) = sum_x xi^d * exp(-i p*x) * f(x)`.

Thus the delta at one fine site, normalized against the `xi^d` counting
measure, has Fourier value `exp(-i p*y)`.  This file specializes the complete
alias-fibre solution of (2.46) to that source and synthesizes the corresponding
fine-to-fine endpoint integrand before the Brillouin integral.

Both endpoints are fine-lattice physical coordinates.  No `Q_j^*` averaging
amplitude is inserted into the source.  This is precisely the source-role
distinction between the full `G_j` needed in (2.42) and the typed
`G_j Q_j^*` kernel already sealed from (2.48).

This module does not yet prove integrability, the normalized inverse
transform, the multiple-reflection formula (2.42), a regional Green identity,
or window 15.  It must not enter the root graph before its own compiler gate.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Literal Fourier transform on `xi * Z^d` with the source normalization
printed in CMP89 (2.43). -/
def cmp89Eq243FineLatticeFourierTransform
    (d : ℕ) (xi : ℝ) (p : Fin d → ℂ)
    (f : (Fin d → ℤ) → ℂ) : ℂ :=
  ∑' x : Fin d → ℤ,
    (xi : ℂ) ^ d *
      Complex.exp
        (-Complex.I *
          cmp89Eq251EntirePhase p
            (cmp89Eq249PhysicalFineLatticeDisplacement xi x)) *
      f x

/-- Delta at one fine site normalized against the `xi^d` counting measure. -/
def cmp89Eq243NormalizedFinePointSource
    (d : ℕ) (xi : ℝ) (source : Fin d → ℤ) :
    (Fin d → ℤ) → ℂ :=
  fun x => if x = source then ((xi : ℂ) ^ d)⁻¹ else 0

/-- The Fourier transform of the normalized fine delta is the literal source
phase in the arbitrary-source equation (2.46). -/
theorem cmp89Eq243FineLatticeFourierTransform_normalizedPointSource
    (d : ℕ) (xi : ℝ) (hxi : xi ≠ 0)
    (p : Fin d → ℂ) (source : Fin d → ℤ) :
    cmp89Eq243FineLatticeFourierTransform d xi p
        (cmp89Eq243NormalizedFinePointSource d xi source) =
      Complex.exp
        (-Complex.I *
          cmp89Eq251EntirePhase p
            (cmp89Eq249PhysicalFineLatticeDisplacement xi source)) := by
  rw [cmp89Eq243FineLatticeFourierTransform, tsum_eq_single source]
  · have hxiC : (xi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxi
    have hpow : (xi : ℂ) ^ d ≠ 0 := pow_ne_zero d hxiC
    simp only [cmp89Eq243NormalizedFinePointSource, if_pos]
    calc
      _ = (((xi : ℂ) ^ d) * (((xi : ℂ) ^ d)⁻¹)) *
          Complex.exp
            (-Complex.I *
              cmp89Eq251EntirePhase p
                (cmp89Eq249PhysicalFineLatticeDisplacement xi source)) := by
            ring
      _ = _ := by rw [mul_inv_cancel₀ hpow, one_mul]
  · intro x hx
    simp [cmp89Eq243NormalizedFinePointSource, hx]

/-- Fourier vector of one fine point source, with the source normalized
against the `xi^d` counting measure in CMP89 (2.43). -/
def cmp89Eq246FinePointSourceAliasVector
    (d L j : ℕ) (z : Fin d → ℂ)
    (sourceEndpoint : Fin d → ℝ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  fun n =>
    Complex.exp
      (-Complex.I *
        cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z n.1) sourceEndpoint)

/-- The named alias source vector is not an independently chosen family: at a
physical fine site it is exactly the Fourier transform (2.43) of the
normalized fine delta. -/
theorem cmp89Eq246FinePointSourceAliasVector_eq_fourierTransform
    (d L j : ℕ) (xi : ℝ) (hxi : xi ≠ 0) (z : Fin d → ℂ)
    (source : Fin d → ℤ) (n : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246FinePointSourceAliasVector d L j z
        (cmp89Eq249PhysicalFineLatticeDisplacement xi source) n =
      cmp89Eq243FineLatticeFourierTransform d xi
        (cmp89Eq248EntireAliasMomentum z n.1)
        (cmp89Eq243NormalizedFinePointSource d xi source) := by
  rw [cmp89Eq243FineLatticeFourierTransform_normalizedPointSource
    d xi hxi (cmp89Eq248EntireAliasMomentum z n.1) source]
  rfl

/-- Nonvanishing of the central holomorphic averaging pair forces the row
factor used by the complete solution to be nonzero.  This keeps `hrow` from
becoming an independent physical input: the later strip producer only has to
control the already named central pair. -/
theorem cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero
    (d L j : ℕ) [NeZero L] (z : Fin d → ℂ)
    (hpair : cmp89Eq249CentralEntireAveragePair d L j z ≠ 0) :
    cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0 := by
  have hzeroMomentum :
      cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d) = z := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum, cmp89Eq249ZeroAlias,
      cmp89Eq245AliasShift]
  have hproduct :
      cmp89Eq246EntireAliasAverageColumn d L j z
          (cmp89Eq249CentralAliasIndex d L j) *
        cmp89Eq246EntireAliasAverageRow d L j z
          (cmp89Eq249CentralAliasIndex d L j) =
        cmp89Eq249CentralEntireAveragePair d L j z := by
    change cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) *
        cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (-cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) =
      cmp89Eq245EntireAverageAmplitude d (L ^ j) z *
        cmp89Eq245EntireAverageAmplitude d (L ^ j) (-z)
    rw [hzeroMomentum]
  intro hrow
  apply hpair
  rw [← hproduct, hrow, mul_zero]

/-- The complete alias-fibre solution of (2.46) for one normalized fine
point source.  Unlike (2.48), this definition inserts no averaging column. -/
def cmp89Eq246StabilizedFinePointSourceSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (sourceEndpoint : Fin d → ℝ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  cmp89Eq246StabilizedAliasFullSolution d L j mass a z
    (cmp89Eq246FinePointSourceAliasVector d L j z sourceEndpoint)

/-- The internally constructed fine-point-source solution solves the literal
diagonal-plus-rank-one fibre system (2.46). -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (sourceEndpoint : Fin d → ℝ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hrow : cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (cmp89Eq246StabilizedFinePointSourceSolution
          d L j mass a z sourceEndpoint) =
      cmp89Eq246FinePointSourceAliasVector d L j z sourceEndpoint := by
  exact
    cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedFullSolution
      d L j mass a z
      (cmp89Eq246FinePointSourceAliasVector d L j z sourceEndpoint)
      hfine hstabilized hrow

/-- Physical-facing form of the point-source equation.  The central row
nonvanishing is discharged from the named opposite-momentum pair rather than
accepted as an unrelated hypothesis. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution_of_pair_ne_zero
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (sourceEndpoint : Fin d → ℝ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hpair : cmp89Eq249CentralEntireAveragePair d L j z ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (cmp89Eq246StabilizedFinePointSourceSolution
          d L j mass a z sourceEndpoint) =
      cmp89Eq246FinePointSourceAliasVector d L j z sourceEndpoint := by
  exact
    cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution
      d L j mass a z sourceEndpoint hfine hstabilized
      (cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero d L j z hpair)

/-- Fully source-tied form of (2.46): the internally constructed solution is
driven by the Fourier transform (2.43) of one normalized fine-lattice delta.
Neither the alias source family nor its endpoint phase is supplied freely. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_normalizedFinePointSourceSolution
    (d L j : ℕ) [NeZero L] (xi : ℝ) (hxi : xi ≠ 0)
    (mass a : ℝ) (z : Fin d → ℂ) (source : Fin d → ℤ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hpair : cmp89Eq249CentralEntireAveragePair d L j z ≠ 0) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (cmp89Eq246StabilizedFinePointSourceSolution d L j mass a z
          (cmp89Eq249PhysicalFineLatticeDisplacement xi source)) =
      fun n =>
        cmp89Eq243FineLatticeFourierTransform d xi
          (cmp89Eq248EntireAliasMomentum z n.1)
          (cmp89Eq243NormalizedFinePointSource d xi source) := by
  calc
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (cmp89Eq246StabilizedFinePointSourceSolution d L j mass a z
          (cmp89Eq249PhysicalFineLatticeDisplacement xi source)) =
      cmp89Eq246FinePointSourceAliasVector d L j z
        (cmp89Eq249PhysicalFineLatticeDisplacement xi source) :=
          cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution_of_pair_ne_zero
            d L j mass a z
              (cmp89Eq249PhysicalFineLatticeDisplacement xi source)
              hfine hstabilized hpair
    _ = fun n =>
        cmp89Eq243FineLatticeFourierTransform d xi
          (cmp89Eq248EntireAliasMomentum z n.1)
          (cmp89Eq243NormalizedFinePointSource d xi source) := by
      funext n
      exact cmp89Eq246FinePointSourceAliasVector_eq_fourierTransform
        d L j xi hxi z source n

/-- The common physical strip gates discharge every nonvanishing premise of
the normalized fine-point-source equation.  In particular the central row is
not exposed to the consumer. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_normalizedFinePointSourceSolution_of_commonRadius
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (source : Fin 4 → ℤ) :
    (cmp89Eq246EntireAliasPrecisionMatrix 4 L j mass a z).mulVec
        (cmp89Eq246StabilizedFinePointSourceSolution 4 L j mass a z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) source)) =
      fun n =>
        cmp89Eq243FineLatticeFourierTransform 4
          (cmp89Eq249FineLatticeSpacing L j)
          (cmp89Eq248EntireAliasMomentum z n.1)
          (cmp89Eq243NormalizedFinePointSource 4
            (cmp89Eq249FineLatticeSpacing L j) source) := by
  have hfine : ∀ m : CMP89Eq246AliasIndex 4 L j,
      m ≠ cmp89Eq249CentralAliasIndex 4 L j →
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m ≠ 0 := by
    intro m hm
    have hm0 : m.1 ≠ cmp89Eq249ZeroAlias 4 := by
      intro hm0
      apply hm
      apply Subtype.ext
      exact hm0
    have hmErase :
        m.1 ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
          (cmp89Eq249ZeroAlias 4) := Finset.mem_erase.mpr ⟨hm0, m.2⟩
    exact cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
      hrho hradius hmErase hp hreal himag
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero
      ha hmassPos hrho hradius hmass hdenWindow hp hreal himag hamplitude
  have hpair : cmp89Eq249CentralEntireAveragePair 4 L j z ≠ 0 :=
    cmp89Eq249CentralEntireAveragePair_ne_zero
      hrho hpairWindow hp hreal himag
  exact
    cmp89Eq246EntireAliasPrecisionMatrix_mulVec_normalizedFinePointSourceSolution
      4 L j (cmp89Eq249FineLatticeSpacing L j)
      (ne_of_gt (cmp89Eq249FineLatticeSpacing_pos L j))
      mass a z source hfine hstabilized hpair

/-- Fine-to-fine Fourier integrand obtained by inverse-transforming every
output alias of the point-source solution.  The target and source coordinates
remain separate: the rank-one correction in (2.46) couples alias phases and
must not be replaced definitionally by the one-displacement (2.48) formula. -/
def cmp89Eq246StabilizedFineToFineGreenIntegrand
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (targetEndpoint sourceEndpoint : Fin d → ℝ) : ℂ :=
  ∑ m : CMP89Eq246AliasIndex d L j,
    Complex.exp
        (Complex.I *
          cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
      cmp89Eq246StabilizedFinePointSourceSolution
        d L j mass a z sourceEndpoint m

/-- The integrand exposes the literal fine point-source vector and the full
alias solution; in particular, there is no hidden `Q_j^*` source factor. -/
theorem cmp89Eq246StabilizedFineToFineGreenIntegrand_eq
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (targetEndpoint sourceEndpoint : Fin d → ℝ) :
    cmp89Eq246StabilizedFineToFineGreenIntegrand
        d L j mass a z targetEndpoint sourceEndpoint =
      ∑ m : CMP89Eq246AliasIndex d L j,
        Complex.exp
            (Complex.I *
              cmp89Eq251EntirePhase
                (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
      cmp89Eq246StabilizedAliasFullSolution d L j mass a z
            (cmp89Eq246FinePointSourceAliasVector
              d L j z sourceEndpoint) m := by
  rfl

/-- Literal same-fine-lattice specialization of the full Green integrand.
Both endpoints use the one spacing fixed by CMP89 at depth `j`; unlike the
typed (2.48) lane, no coarse endpoint or `Q_j^*` source is present. -/
def cmp89Eq246PhysicalFineToFineGreenIntegrand
    (L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin 4 → ℂ)
    (target source : Fin 4 → ℤ) : ℂ :=
  let xi := cmp89Eq249FineLatticeSpacing L j
  cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a z
    (cmp89Eq249PhysicalFineLatticeDisplacement xi target)
    (cmp89Eq249PhysicalFineLatticeDisplacement xi source)

/-- The physical wrapper keeps the two fine endpoints separate in the full
alias solution.  It does not collapse them to the one-displacement (2.48)
formula. -/
theorem cmp89Eq246PhysicalFineToFineGreenIntegrand_eq
    (L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin 4 → ℂ)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand
        L j mass a z target source =
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source) := by
  rfl

end

end YangMills.RG
