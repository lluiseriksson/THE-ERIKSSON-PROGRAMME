/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SectionCPointedFactorDictionary
import YangMills.RG.BalabanCMP99SectionCCollarGap

/-!
# Honest insertion of the first verified nonzero CMP99 Section-C species

CMP99 lists examples followed by "etc.", so the still-open factor alphabet
must remain explicit.  We extend the already source-faithful pointed label by
one verified slot:

* `none`: the printed zero factor;
* `some (Sum.inl ())`: the verified covariance difference;
* `some (Sum.inr alpha)`: an open remaining factor.

The construction lifts an existing pointed dictionary and therefore preserves
its two exact zero-factor equations.  It does not enumerate, identify, or
constrain the open `Other` species.
-/

namespace YangMills.RG

noncomputable section

universe u v

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The printed zero, one verified nonzero species, and an open remainder. -/
abbrev CMP99SectionCFirstVerifiedLabel (Other : Type u) :=
  CMP99SectionCFactorLabel (Sum Unit Other)

/-- Literal label of the verified covariance-difference species. -/
def cmp99SectionCCovarianceDifferenceLabel {Other : Type u} :
    CMP99SectionCFirstVerifiedLabel Other :=
  some (Sum.inl ())

/-- Injection of an unresolved source factor into the open remainder. -/
def cmp99SectionCOpenFactorLabel {Other : Type u} (alpha : Other) :
    CMP99SectionCFirstVerifiedLabel Other :=
  some (Sum.inr alpha)

@[simp] theorem card_cmp99SectionCFirstVerifiedLabel
    (Other : Type u) [Fintype Other] :
    Fintype.card (CMP99SectionCFirstVerifiedLabel Other) =
      Fintype.card Other + 2 := by
  simp [CMP99SectionCFirstVerifiedLabel, CMP99SectionCFactorLabel,
    Nat.add_comm]
  omega

namespace CMP99SectionCPointedFactorDictionary

/-- Add one named verified species to an existing honest pointed dictionary.
The old open factors are injected into the right summand unchanged. -/
noncomputable def withVerifiedSpecies
    {Other : Type u} {Q S : ℕ} [NeZero Q] [NeZero S]
    {E : Type v} [Zero E]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S E)
    (verified :
      CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S → E) :
    CMP99SectionCPointedFactorDictionary (Sum Unit Other) Q S E where
  Rop label X :=
    match label with
    | none => Base.Rop cmp99SectionCZeroLabel X
    | some (Sum.inl _) => verified X
    | some (Sum.inr alpha) => Base.Rop (some alpha) X
  sourceCellHead := Base.sourceCellHead
  zero_on_sourceCell := by
    intro cell
    exact Base.zero_on_sourceCell cell
  zero_off_sourceCell := by
    intro X hX
    exact Base.zero_off_sourceCell X hX

@[simp] theorem withVerifiedSpecies_Rop_zero
    {Other : Type u} {Q S : ℕ} [NeZero Q] [NeZero S]
    {E : Type v} [Zero E]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S E)
    (verified :
      CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S → E)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (Base.withVerifiedSpecies verified).Rop cmp99SectionCZeroLabel X =
      Base.Rop cmp99SectionCZeroLabel X :=
  rfl

@[simp] theorem withVerifiedSpecies_Rop_verified
    {Other : Type u} {Q S : ℕ} [NeZero Q] [NeZero S]
    {E : Type v} [Zero E]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S E)
    (verified :
      CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S → E)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (Base.withVerifiedSpecies verified).Rop
        cmp99SectionCCovarianceDifferenceLabel X = verified X :=
  rfl

@[simp] theorem withVerifiedSpecies_Rop_open
    {Other : Type u} {Q S : ℕ} [NeZero Q] [NeZero S]
    {E : Type v} [Zero E]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S E)
    (verified :
      CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S → E)
    (alpha : Other)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (Base.withVerifiedSpecies verified).Rop
        (cmp99SectionCOpenFactorLabel alpha) X = Base.Rop (some alpha) X :=
  rfl

/-- Specialize the verified slot to the literal physical covariance
difference.  Support families remain chart data; nesting is required only by
the decay theorem, not by this definition. -/
noncomputable def withCovarianceDifference
    {Other : Type u} {Q S d N Nc : ℕ}
    [NeZero Q] [NeZero S] [NeZero N]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S
      (PhysicalEndomorphism d N Nc))
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : CMP99SimpleLocalizationDomain
      (cmp116CoarseFaceAdj 4 Q) S → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hcoercive : IsCoerciveCLM K c) :
    CMP99SectionCPointedFactorDictionary (Sum Unit Other) Q S
      (PhysicalEndomorphism d N Nc) :=
  Base.withVerifiedSpecies fun X =>
    cmp99SectionCCovarianceDifference K (S0 X) (S1 X)
      hc hmass hcoercive

@[simp] theorem withCovarianceDifference_Rop_verified
    {Other : Type u} {Q S d N Nc : ℕ}
    [NeZero Q] [NeZero S] [NeZero N]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S
      (PhysicalEndomorphism d N Nc))
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : CMP99SimpleLocalizationDomain
      (cmp116CoarseFaceAdj 4 Q) S → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hcoercive : IsCoerciveCLM K c)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (Base.withCovarianceDifference K S0 S1 hc hmass hcoercive).Rop
        cmp99SectionCCovarianceDifferenceLabel X =
      cmp99SectionCCovarianceDifference K (S0 X) (S1 X)
        hc hmass hcoercive :=
  rfl

/-- The newly inserted literal label inherits the fully explicit common-collar
decay theorem.  No claim is made for labels in the open right summand. -/
theorem norm_Rop_covarianceDifferenceLabel_le_of_commonShellGap
    {Other : Type u} {Q S d N Nc : ℕ}
    [NeZero Q] [NeZero S] [NeZero N]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S
      (PhysicalEndomorphism d N Nc))
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : CMP99SimpleLocalizationDomain
      (cmp116CoarseFaceAdj 4 Q) S → Finset (PhysicalBond d N))
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    (hsub : S1 X ⊆ S0 X)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {CK NR c mass A0 A1 mu : ℝ}
    (hCK : 0 ≤ CK) (hNR : 0 ≤ NR)
    (hkernel : PhysicalCovarianceKernelBound K (fun _ _ => CK))
    (hball : ∀ source : PhysicalBond d N,
      (((Finset.univ.filter fun target =>
        physicalBondDist target source ≤ R).card : ℕ) : ℝ) ≤ NR)
    (hc : 0 < c) (hmass : 0 < mass) (hcoercive : IsCoerciveCLM K c)
    (hC0 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K (S0 X) hc hmass hcoercive)
      physicalBondDist A0 mu)
    (hC1 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K (S1 X) hc hmass hcoercive)
      physicalBondDist A1 mu)
    {source target : PhysicalBond d N} {L : ℕ}
    (htarget : target ∈ cmp99PhysicalBondShellGap
      physicalBondDist (S0 X \ S1 X) R L)
    (hsource : source ∈ cmp99PhysicalBondShellGap
      physicalBondDist (S0 X \ S1 X) R L)
    (v0 : SUNLieCoord Nc) :
    ‖(Base.withCovarianceDifference K S0 S1 hc hmass hcoercive).Rop
        cmp99SectionCCovarianceDifferenceLabel X
        (singlePhysicalBondCochain source v0) target‖ ≤
      A0 * A1 * ((3 * CK * NR + |mass|) * (S0 X \ S1 X).card) *
        Real.exp (-(2 * mu * (L : ℝ))) * ‖v0‖ := by
  simpa using
    (cmp99SectionCCovarianceDifference_bilateralDecay_of_commonShellGap
      K hsub R hrange hCK hNR hkernel hball hc hmass hcoercive hC0 hC1
        htarget hsource v0)

end CMP99SectionCPointedFactorDictionary

end

end YangMills.RG
