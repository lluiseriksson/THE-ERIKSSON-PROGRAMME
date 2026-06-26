/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3ScaleFamily

/-!
# CMP116 equation (2.37) post-P majorization boundary

This module isolates the final post-`P` majorization supported by CMP116
equation (2.37), the following summation paragraph, and the displayed `C3`
shape on page 20.

Honest scope: this file does not prove the combined post-`P` source sum, does
not identify the dependent `Z0/Z0'` source indices with the repository
indices, and does not assign numerical values to any source `O(1)` constant.
It only packages a source-shaped exponent-absorption inequality and an
explicit amplitude comparison into the existing
`CMP116PostPResidualSourceMajorizationScaleFamily` consumer.
-/

namespace YangMills.RG

open scoped BigOperators

/-- The fixed-`Z0'` family reached from the repository's dependent
`Z0 -> Z0'` post-`P` indexing at fixed `(Z,D,P)`.

This is only a finite reindexing device: identifying it with the source
`Z0'` family remains an explicit dictionary hypothesis. -/
def cmp116Eq237Z0PrimeIndex
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (Z : σ) (D : ιD) (P : ιP) : Finset ιZ0' :=
  (R.Z0Index Z D P).biUnion
    (fun Z0 => R.Z0PrimeIndex Z D P Z0)

/-- Repository-level fixed-`Z` `Z0'` family obtained by taking the finite union
over all `(D,P)` branches.

This is a bookkeeping index for Lean's dependent post-`P` family.  Identifying
it with Balaban's source `Z0'` summation family remains a separate source
dictionary theorem. -/
def cmp116Eq237GlobalZ0PrimeIndex
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (Z : σ) : Finset ιZ0' :=
  (R.DIndex Z).biUnion
    (fun D =>
      (R.PIndex Z D).biUnion
        (fun P => cmp116Eq237Z0PrimeIndex R Z D P))

/-- Every fixed `(D,P)` `Z0'` family is contained in the repository-level
fixed-`Z` union.

This discharges only the finite bookkeeping inclusion.  It does not identify
the repository union with the source index family used after CMP116 Eq. (2.37). -/
theorem cmp116Eq237Z0PrimeIndex_subset_global
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (Z : σ) (D : ιD) (P : ιP)
    (hD : D ∈ R.DIndex Z)
    (hP : P ∈ R.PIndex Z D) :
    cmp116Eq237Z0PrimeIndex R Z D P ⊆
      cmp116Eq237GlobalZ0PrimeIndex R Z := by
  intro Z0' hZ0'
  rw [cmp116Eq237GlobalZ0PrimeIndex, Finset.mem_biUnion]
  exact ⟨D, hD, by
    rw [Finset.mem_biUnion]
    exact ⟨P, hP, hZ0'⟩⟩

/-- The `Z0` fiber over a fixed `Z0'` in the post-`P` reindexing. -/
def cmp116Eq237Z0Fiber
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (Z : σ) (D : ιD) (P : ιP) (Z0' : ιZ0') : Finset ιZ0 :=
  (R.Z0Index Z D P).filter
    (fun Z0 => Z0' ∈ R.Z0PrimeIndex Z D P Z0)

/-- Finite transposition of the repository's dependent post-`P`
`Z0/Z0'` sum into fixed-`Z0'` fibers.

The proof is pure finite Fubini/reindexing.  It does not assert any analytic
estimate and does not identify the reindexed family with Balaban's source
objects. -/
theorem cmp116Eq237_nested_sum_eq_fiber_sum
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (Z : σ) (D : ιD) (P : ιP)
    (f : ιZ0 → ιZ0' → ℝ) :
    Finset.sum (R.Z0Index Z D P) (fun Z0 =>
      Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0p =>
        f Z0 Z0p)) =
      Finset.sum (cmp116Eq237Z0PrimeIndex R Z D P) (fun Z0p =>
        Finset.sum (cmp116Eq237Z0Fiber R Z D P Z0p) (fun Z0 =>
          f Z0 Z0p)) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _hx => ⟨x.snd, x.fst⟩)
    (fun x _hx => ⟨x.snd, x.fst⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_sigma]
    have hx' := (Finset.mem_sigma).mp hx
    constructor
    · rw [cmp116Eq237Z0PrimeIndex, Finset.mem_biUnion]
      exact ⟨x.fst, hx'.1, hx'.2⟩
    · rw [cmp116Eq237Z0Fiber, Finset.mem_filter]
      exact ⟨hx'.1, hx'.2⟩
  · intro x hx
    rw [Finset.mem_sigma]
    have hx' := (Finset.mem_sigma).mp hx
    have hfiber := hx'.2
    rw [cmp116Eq237Z0Fiber, Finset.mem_filter] at hfiber
    exact ⟨hfiber.1, hfiber.2⟩
  · intro x _hx
    cases x
    rfl
  · intro x _hx
    cases x
    rfl
  · intro x _hx
    rfl

/-- The explicit Eq. (2.37) amplitude kept before comparison with
`C3 * epsilon1`.  The source audit keeps the `O(1)` constant represented by
`C237` separate from the other `O(1)` constants. -/
def cmp116Eq237Amplitude
    (blockScale : ℕ) (C237 epsilon2 : ℝ) : ℝ :=
  2 * (((blockScale : ℝ) + 2) ^ 4) * C237 * epsilon2

theorem cmp116Eq237Amplitude_nonneg
    (blockScale : ℕ) {C237 epsilon2 : ℝ}
    (hC237_nonneg : 0 ≤ C237)
    (hepsilon2_nonneg : 0 ≤ epsilon2) :
    0 ≤ cmp116Eq237Amplitude blockScale C237 epsilon2 := by
  unfold cmp116Eq237Amplitude
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (by positivity))
        hC237_nonneg)
      hepsilon2_nonneg

/-- Literal fixed-`Z0'` Eq. (2.37) source majorant.

The fields are deliberately dictionary-shaped: `gapCard` represents
`|Z \ Z0'|`, `components` the connected components of the support of `Z0'`,
and `componentMetric` the source `d_{k+1}` metric on those components. -/
noncomputable def cmp116Eq237FixedZ0PrimeWeight
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (Z : σ) (Z0' : ιZ0') : ℝ :=
  Real.exp
      (-((hp.kappa1 - 1) *
        (((localizationScale : ℝ) ^ 4)⁻¹) *
          (gapCard Z Z0' : ℝ))) *
    (Finset.prod (components Z Z0') (fun Zi =>
      cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
        Real.exp
          (-(((1 - 7 * hp.delta) / 2) *
            (hp.blockScale : ℝ) * hp.kappa *
              (componentMetric Z Z0' Zi : ℝ))))) *
    Real.exp (Calpha5 * alpha5 * (sourceCard Z : ℝ))

theorem cmp116Eq237FixedZ0PrimeWeight_nonneg
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (hC237_nonneg : 0 ≤ C237)
    (Z : σ) (Z0' : ιZ0') :
    0 ≤
      cmp116Eq237FixedZ0PrimeWeight
        hp localizationScale C237 Calpha5 alpha5
        sourceCard gapCard components componentMetric Z Z0' := by
  classical
  unfold cmp116Eq237FixedZ0PrimeWeight
  have hA :
      0 ≤ cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 :=
    cmp116Eq237Amplitude_nonneg
      hp.blockScale hC237_nonneg hp.epsilon2_nonneg
  exact
    mul_nonneg
      (mul_nonneg
        (le_of_lt (Real.exp_pos _))
        (Finset.prod_nonneg
          (fun Zi _hZi =>
            mul_nonneg hA (le_of_lt (Real.exp_pos _)))))
      (le_of_lt (Real.exp_pos _))

/-- Eq. (2.37), supplied as fixed-`Z0'` estimates after factoring the
repository's fixed-`(D,P)` P-weight, plus the post-(2.37) final summation,
implies the combined post-`P` source bound consumed downstream. -/
theorem cmp116PostPResidualSourceBound_of_eq237
    {σ ιD ιP ιZ0 ιZ0' ιC Ψ Φ : Type*}
    [DecidableEq ιZ0']
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (sourceZ0PrimeIndex : σ → Finset ιZ0')
    (postPSourceWeight : σ → ℝ)
    (pWeight : σ → ιD → ιP → ℝ)
    (hC237_nonneg : 0 ≤ C237)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          0 ≤ pWeight Z D P)
    (hindex :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          cmp116Eq237Z0PrimeIndex R Z D P ⊆
            sourceZ0PrimeIndex Z)
    (heq237_fixed :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex R Z D P →
              Finset.sum (cmp116Eq237Z0Fiber R Z D P Z0') (fun Z0 =>
                  R.termWeight Z D P Z0 Z0') ≤
                pWeight Z D P *
                  cmp116Eq237FixedZ0PrimeWeight
                    hp localizationScale C237 Calpha5 alpha5
                    sourceCard gapCard components componentMetric Z Z0')
    (hpost_eq237 :
      ∀ Z,
        Finset.sum (sourceZ0PrimeIndex Z) (fun Z0' =>
            cmp116Eq237FixedZ0PrimeWeight
              hp localizationScale C237 Calpha5 alpha5
              sourceCard gapCard components componentMetric Z Z0') ≤
          cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
            postPSourceWeight Z) :
    CMP116PostPResidualSourceBound
      R
      postPSourceWeight
      (cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2)
      pWeight := by
  intro Z D hD P hP
  let W : ιZ0' → ℝ :=
    fun Z0' =>
      cmp116Eq237FixedZ0PrimeWeight
        hp localizationScale C237 Calpha5 alpha5
        sourceCard gapCard components componentMetric Z Z0'
  have hW_nonneg :
      ∀ Z0', 0 ≤ W Z0' := by
    intro Z0'
    exact
      cmp116Eq237FixedZ0PrimeWeight_nonneg
        hp localizationScale C237 Calpha5 alpha5
        sourceCard gapCard components componentMetric
        hC237_nonneg Z Z0'
  have hsubset_sum :
      Finset.sum (cmp116Eq237Z0PrimeIndex R Z D P) (fun Z0' => W Z0') ≤
        Finset.sum (sourceZ0PrimeIndex Z) (fun Z0' => W Z0') := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (hindex Z D hD P hP)
        (fun Z0' _hZ0' _hnot => hW_nonneg Z0')
  have hp_nonneg : 0 ≤ pWeight Z D P :=
    hpWeight_nonneg Z D hD P hP
  calc
    Finset.sum (R.Z0Index Z D P) (fun Z0 =>
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0')) =
      Finset.sum (cmp116Eq237Z0PrimeIndex R Z D P) (fun Z0' =>
        Finset.sum (cmp116Eq237Z0Fiber R Z D P Z0') (fun Z0 =>
          R.termWeight Z D P Z0 Z0')) := by
        exact
          cmp116Eq237_nested_sum_eq_fiber_sum
            R Z D P (fun Z0 Z0' => R.termWeight Z D P Z0 Z0')
    _ ≤
      Finset.sum (cmp116Eq237Z0PrimeIndex R Z D P) (fun Z0' =>
        pWeight Z D P * W Z0') := by
        exact
          Finset.sum_le_sum
            (fun Z0' hZ0' =>
              by
                simpa [W] using
                  heq237_fixed Z D hD P hP Z0' hZ0')
    _ =
      pWeight Z D P *
        Finset.sum (cmp116Eq237Z0PrimeIndex R Z D P) (fun Z0' => W Z0') := by
        simpa using
          (Finset.mul_sum
            (cmp116Eq237Z0PrimeIndex R Z D P) W
            (pWeight Z D P)).symm
    _ ≤
      pWeight Z D P *
        Finset.sum (sourceZ0PrimeIndex Z) (fun Z0' => W Z0') := by
        exact mul_le_mul_of_nonneg_left hsubset_sum hp_nonneg
    _ ≤
      pWeight Z D P *
        (cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
          postPSourceWeight Z) := by
        exact
          mul_le_mul_of_nonneg_left
            (by simpa [W] using hpost_eq237 Z)
            hp_nonneg
    _ =
      (cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
        postPSourceWeight Z) *
          pWeight Z D P := by
        ring

/-- Variant of `cmp116PostPResidualSourceBound_of_eq237` using the repository's
global fixed-`Z` `Z0'` union as the final summation family.

This removes the finite inclusion input `hindex` for this particular
bookkeeping choice.  It still requires the fixed-`Z0'` Eq. (2.37) estimate and
the final post-(2.37) summation over the global union, and it does not identify
that union with Balaban's source `Z0'` family. -/
theorem cmp116PostPResidualSourceBound_of_eq237_globalIndex
    {σ ιD ιP ιZ0 ιZ0' ιC Ψ Φ : Type*}
    [DecidableEq ιZ0']
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (postPSourceWeight : σ → ℝ)
    (pWeight : σ → ιD → ιP → ℝ)
    (hC237_nonneg : 0 ≤ C237)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          0 ≤ pWeight Z D P)
    (heq237_fixed :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex R Z D P →
              Finset.sum (cmp116Eq237Z0Fiber R Z D P Z0') (fun Z0 =>
                  R.termWeight Z D P Z0 Z0') ≤
                pWeight Z D P *
                  cmp116Eq237FixedZ0PrimeWeight
                    hp localizationScale C237 Calpha5 alpha5
                    sourceCard gapCard components componentMetric Z Z0')
    (hpost_eq237 :
      ∀ Z,
        Finset.sum (cmp116Eq237GlobalZ0PrimeIndex R Z) (fun Z0' =>
            cmp116Eq237FixedZ0PrimeWeight
              hp localizationScale C237 Calpha5 alpha5
              sourceCard gapCard components componentMetric Z Z0') ≤
          cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
            postPSourceWeight Z) :
    CMP116PostPResidualSourceBound
      R
      postPSourceWeight
      (cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2)
      pWeight := by
  exact
    cmp116PostPResidualSourceBound_of_eq237
      hp R localizationScale C237 Calpha5 alpha5
      sourceCard gapCard components componentMetric
      (cmp116Eq237GlobalZ0PrimeIndex R)
      postPSourceWeight pWeight hC237_nonneg hpWeight_nonneg
      (fun Z D hD P hP =>
        cmp116Eq237Z0PrimeIndex_subset_global R Z D P hD hP)
      heq237_fixed hpost_eq237

/-- Source-shaped Eq. (2.37) majorization boundary for the post-`P` stage.

The field `residualExponent` represents the leftover page-20 exponential
factor, including the `alpha5`/cardinality contribution and any other residual
terms that must be absorbed into the reserve between the source
`(1 - 7*delta)/2` decay and the canonical Lemma-3 `(1 - 8*delta)/2` decay.

The amplitude comparison is deliberately stated directly as
`postPAmplitude <= C3*epsilon1`; distinct source occurrences of `O(1)` must be
majorized before this boundary is instantiated. -/
structure CMP116Eq237MajorizationBoundary
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ) where

  residualExponent : ∀ t k, σ t k → ℝ

  amplitude_nonneg :
    ∀ t k, 0 ≤ postPAmplitude t k

  amplitude_le_C3 :
    ∀ t k,
      postPAmplitude t k ≤
        (hp t k).C3 * (hp t k).epsilon1

  seven_delta_bound :
    ∀ t k Z,
      postPSourceWeight t k Z ≤
        Real.exp
          (residualExponent t k Z -
            ((1 - 7 * (hp t k).delta) / 2) *
              ((hp t k).blockScale : ℝ) *
              (hp t k).kappa *
              (sourceMetric t k Z : ℝ))

  residual_absorbed :
    ∀ t k Z,
      residualExponent t k Z ≤
        ((hp t k).delta / 2) *
          ((hp t k).blockScale : ℝ) *
          (hp t k).kappa *
          (sourceMetric t k Z : ℝ)

/-- Absorb the Eq. (2.37) residual exponent into the reserve between
`(1 - 7*delta)/2` and the canonical Lemma-3 `(1 - 8*delta)/2` decay. -/
theorem cmp116Eq237_residualExponent_absorbed
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (h :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude) :
    ∀ t k Z,
      postPSourceWeight t k Z ≤
        balabanCMP116Lemma3Weight
          (hp t k).blockScale
          (hp t k).delta
          (hp t k).kappa
          (sourceMetric t k)
          Z := by
  intro t k Z
  let m : ℝ := (sourceMetric t k Z : ℝ)
  let sourceArg : ℝ :=
    h.residualExponent t k Z -
      ((1 - 7 * (hp t k).delta) / 2) *
        ((hp t k).blockScale : ℝ) *
        (hp t k).kappa *
        m
  let absorbedArg : ℝ :=
    ((hp t k).delta / 2) *
      ((hp t k).blockScale : ℝ) *
      (hp t k).kappa *
      m -
    ((1 - 7 * (hp t k).delta) / 2) *
      ((hp t k).blockScale : ℝ) *
      (hp t k).kappa *
      m
  have hsourceArg_le : sourceArg ≤ absorbedArg := by
    dsimp [sourceArg, absorbedArg, m]
    linarith [h.residual_absorbed t k Z]
  have habsorbedArg :
      absorbedArg =
        -((balabanCMP116Lemma3DecayRate
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa) *
          (sourceMetric t k Z : ℝ)) := by
    dsimp [absorbedArg, m, balabanCMP116Lemma3DecayRate]
    ring
  calc
    postPSourceWeight t k Z ≤ Real.exp sourceArg := by
      simpa [sourceArg, m] using h.seven_delta_bound t k Z
    _ ≤ Real.exp absorbedArg := by
      exact Real.exp_le_exp.mpr hsourceArg_le
    _ =
        balabanCMP116Lemma3Weight
          (hp t k).blockScale
          (hp t k).delta
          (hp t k).kappa
          (sourceMetric t k)
          Z := by
      rw [habsorbedArg]
      simp [balabanCMP116Lemma3Weight]

/-- CMP116 Eq. (2.37) post-`P` exponent absorption and the displayed `C3`
amplitude comparison imply the canonical post-`P` majorization consumed by the
Lemma-3 scale-family interface. -/
theorem cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (h :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude) :
    CMP116PostPResidualSourceMajorizationScaleFamily
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      postPSourceWeight
      postPAmplitude := by
  intro t k Z
  have hweight :
      postPSourceWeight t k Z ≤
        balabanCMP116Lemma3Weight
          (hp t k).blockScale
          (hp t k).delta
          (hp t k).kappa
          (sourceMetric t k)
          Z :=
    cmp116Eq237_residualExponent_absorbed
      hp sourceMetric postPSourceWeight postPAmplitude h t k Z
  calc
    postPAmplitude t k * postPSourceWeight t k Z ≤
        postPAmplitude t k *
          balabanCMP116Lemma3Weight
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa
            (sourceMetric t k)
            Z := by
      exact mul_le_mul_of_nonneg_left hweight (h.amplitude_nonneg t k)
    _ ≤
        ((hp t k).C3 * (hp t k).epsilon1) *
          balabanCMP116Lemma3Weight
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa
            (sourceMetric t k)
            Z := by
      exact
        mul_le_mul_of_nonneg_right
          (h.amplitude_le_C3 t k)
          (balabanCMP116Lemma3Weight_nonneg
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa
            (sourceMetric t k)
            Z)

/-- Build the weighted post-`P` boundary from a combined post-`P` source sum
and the Eq. (2.37)/`C3` majorization boundary.

This removes the independent caller-supplied `postP_majorization` field on
this source-facing route.  The combined finite post-`P` source estimate remains
an explicit input. -/
def CMP116Lemma3WeightedPostPSourceScaleBoundary.of_sourceBound_eq237Majorization
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (hsource :
      ∀ t k,
        CMP116PostPResidualSourceBound
          (R t k)
          (postPSourceWeight t k)
          (postPAmplitude t k)
          (cmp116Eq229WeightedPWeight
            (DParts t k)
            (alpha6 t k)
            (hp t k).delta
            (hp t k).kappa
            (eq229Metric t k)
            (pResidualWeight t k)))
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude) :
    CMP116Lemma3WeightedPostPSourceScaleBoundary
      hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
      postPSourceWeight postPAmplitude where

  postP_source_bound := hsource

  postP_majorization :=
    cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237
      hp sourceMetric postPSourceWeight postPAmplitude hmajorization

/-- Build the weighted post-`P` boundary directly from the fixed-`Z0'`
Eq. (2.37) estimate and the post-(2.37) final summation.

Compared with `of_sourceBound_eq237Majorization`, this constructor removes the
caller-supplied `CMP116PostPResidualSourceBound` premise on the Eq. (2.37)
route.  The remaining analytic inputs are exactly the fixed-`Z0'` estimate,
the inclusion into the canonical source `Z0'` family, the final source
summation, and the separate majorization into the canonical Lemma-3 weight. -/
def CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237
    {σ ιD ιP ιZ0 ιZ0' ιY ιC : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (localizationScale : ℕ → ℕ → ℕ)
    (C237 Calpha5 alpha5 : ℕ → ℕ → ℝ)
    (sourceCard : ∀ t k, σ t k → ℕ)
    (gapCard : ∀ t k, σ t k → ιZ0' t k → ℕ)
    (components : ∀ t k, σ t k → ιZ0' t k → Finset (ιC t k))
    (componentMetric : ∀ t k, σ t k → ιZ0' t k → ιC t k → ℕ)
    (sourceZ0PrimeIndex : ∀ t k, σ t k → Finset (ιZ0' t k))
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (hC237_nonneg : ∀ t k, 0 ≤ C237 t k)
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (hindex :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          cmp116Eq237Z0PrimeIndex (R t k) Z D P ⊆
            sourceZ0PrimeIndex t k Z)
    (heq237_fixed :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex (R t k) Z D P →
              Finset.sum
                  (cmp116Eq237Z0Fiber (R t k) Z D P Z0')
                  (fun Z0 => (R t k).termWeight Z D P Z0 Z0') ≤
                cmp116Eq229WeightedPWeight
                  (DParts t k)
                  (alpha6 t k)
                  (hp t k).delta
                  (hp t k).kappa
                  (eq229Metric t k)
                  (pResidualWeight t k)
                  Z D P *
                  cmp116Eq237FixedZ0PrimeWeight
                    (hp t k)
                    (localizationScale t k)
                    (C237 t k) (Calpha5 t k) (alpha5 t k)
                    (sourceCard t k) (gapCard t k)
                    (components t k) (componentMetric t k) Z Z0')
    (hpost_eq237 :
      ∀ t k Z,
        Finset.sum (sourceZ0PrimeIndex t k Z) (fun Z0' =>
            cmp116Eq237FixedZ0PrimeWeight
              (hp t k)
              (localizationScale t k)
              (C237 t k) (Calpha5 t k) (alpha5 t k)
              (sourceCard t k) (gapCard t k)
              (components t k) (componentMetric t k) Z Z0') ≤
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2 *
            postPSourceWeight t k Z)
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight
        (fun t k =>
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2)) :
    CMP116Lemma3WeightedPostPSourceScaleBoundary
      hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
      postPSourceWeight
      (fun t k =>
        cmp116Eq237Amplitude
          (hp t k).blockScale (C237 t k) (hp t k).epsilon2) where

  postP_source_bound := by
    intro t k
    exact
      cmp116PostPResidualSourceBound_of_eq237
        (hp t k)
        (R t k)
        (localizationScale t k)
        (C237 t k) (Calpha5 t k) (alpha5 t k)
        (sourceCard t k) (gapCard t k)
        (components t k) (componentMetric t k)
        (sourceZ0PrimeIndex t k)
        (postPSourceWeight t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))
        (hC237_nonneg t k)
        (fun Z D _hD P _hP =>
          cmp116Eq229WeightedPWeight_nonneg
            (DParts := DParts t k)
            (metric := eq229Metric t k)
            (pResidualWeight := pResidualWeight t k)
            (halpha6 t k)
            (hpResidual_nonneg t k)
            Z D P)
        (hindex t k)
        (heq237_fixed t k)
        (hpost_eq237 t k)

  postP_majorization :=
    cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237
      hp sourceMetric postPSourceWeight
      (fun t k =>
        cmp116Eq237Amplitude
          (hp t k).blockScale (C237 t k) (hp t k).epsilon2)
      hmajorization

namespace CMP116Lemma3WeightedPostPScaleSourceAssumptions

/-- Build the weighted post-`P` source package from Eq. (2.29), a supplied
P-stage source boundary, the combined post-`P` source sum, the Eq. (2.37)
majorization boundary, and the activity/termwise boundary.

Compared with `of_boundaries`, this route removes the caller-supplied
`CMP116Lemma3WeightedPostPSourceScaleBoundary` package.  The combined post-`P`
source estimate remains explicit, while the canonical post-`P` majorization is
generated from `CMP116Eq237MajorizationBoundary`. -/
def of_eq237Majorization
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (hsource :
      ∀ t k,
        CMP116PostPResidualSourceBound
          (R t k)
          (postPSourceWeight t k)
          (postPAmplitude t k)
          (cmp116Eq229WeightedPWeight
            (DParts t k)
            (alpha6 t k)
            (hp t k).delta
            (hp t k).kappa
            (eq229Metric t k)
            (pResidualWeight t k)))
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    pStage
    (CMP116Lemma3WeightedPostPSourceScaleBoundary.of_sourceBound_eq237Majorization
      hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
      postPSourceWeight postPAmplitude hsource hmajorization)
    activity

/-- Build the weighted post-`P` source package from Eq. (2.29), a P-stage
source boundary, the fixed-`Z0'` Eq. (2.37) estimate, the post-(2.37) source
summation, the Eq. (2.37) majorization boundary, and the activity/termwise
boundary.

This is the source-facing Eq. (2.37) route that removes the caller-supplied
`CMP116PostPResidualSourceBound` field. -/
def of_eq237
    {σ ιD ιP ιZ0 ιZ0' ιY ιC : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {localizationScale : ℕ → ℕ → ℕ}
    {C237 Calpha5 alpha5 : ℕ → ℕ → ℝ}
    {sourceCard : ∀ t k, σ t k → ℕ}
    {gapCard : ∀ t k, σ t k → ιZ0' t k → ℕ}
    {components : ∀ t k, σ t k → ιZ0' t k → Finset (ιC t k)}
    {componentMetric : ∀ t k, σ t k → ιZ0' t k → ιC t k → ℕ}
    {sourceZ0PrimeIndex : ∀ t k, σ t k → Finset (ιZ0' t k)}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (hC237_nonneg : ∀ t k, 0 ≤ C237 t k)
    (hindex :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          cmp116Eq237Z0PrimeIndex (R t k) Z D P ⊆
            sourceZ0PrimeIndex t k Z)
    (heq237_fixed :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex (R t k) Z D P →
              Finset.sum
                  (cmp116Eq237Z0Fiber (R t k) Z D P Z0')
                  (fun Z0 => (R t k).termWeight Z D P Z0 Z0') ≤
                cmp116Eq229WeightedPWeight
                  (DParts t k)
                  (alpha6 t k)
                  (hp t k).delta
                  (hp t k).kappa
                  (eq229Metric t k)
                  (pResidualWeight t k)
                  Z D P *
                  cmp116Eq237FixedZ0PrimeWeight
                    (hp t k)
                    (localizationScale t k)
                    (C237 t k) (Calpha5 t k) (alpha5 t k)
                    (sourceCard t k) (gapCard t k)
                    (components t k) (componentMetric t k) Z Z0')
    (hpost_eq237 :
      ∀ t k Z,
        Finset.sum (sourceZ0PrimeIndex t k Z) (fun Z0' =>
            cmp116Eq237FixedZ0PrimeWeight
              (hp t k)
              (localizationScale t k)
              (C237 t k) (Calpha5 t k) (alpha5 t k)
              (sourceCard t k) (gapCard t k)
              (components t k) (componentMetric t k) Z Z0') ≤
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2 *
            postPSourceWeight t k Z)
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight
        (fun t k =>
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2))
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight
      (fun t k =>
        cmp116Eq237Amplitude
          (hp t k).blockScale (C237 t k) (hp t k).epsilon2) :=
  of_boundaries
    eq229
    pStage
    (CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237
      hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
      localizationScale C237 Calpha5 alpha5
      sourceCard gapCard components componentMetric sourceZ0PrimeIndex
      postPSourceWeight hC237_nonneg
      eq229.alpha6_nonneg pStage.p_residual_weight_nonneg
      hindex heq237_fixed hpost_eq237 hmajorization)
    activity

/-- Direct Lemma-3 scale-family consumer using the Eq. (2.37) majorization
boundary for the weighted post-`P` stage.

This is the estimate-level counterpart of `of_eq237Majorization`: it still
requires Eq. (2.29), the P-stage source boundary, the combined post-`P` source
sum, and the activity/termwise boundary explicitly. -/
def lemma3_activity_estimate_of_eq237Majorization
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (hsource :
      ∀ t k,
        CMP116PostPResidualSourceBound
          (R t k)
          (postPSourceWeight t k)
          (postPAmplitude t k)
          (cmp116Eq229WeightedPWeight
            (DParts t k)
            (alpha6 t k)
            (hp t k).delta
            (hp t k).kappa
            (eq229Metric t k)
            (pResidualWeight t k)))
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  lemma3_activity_estimate
    (of_eq237Majorization eq229 pStage hsource hmajorization activity)

/-- Direct Lemma-3 scale-family consumer for the source-facing Eq. (2.37)
route that theorem-generates the combined post-`P` source bound. -/
def lemma3_activity_estimate_of_eq237
    {σ ιD ιP ιZ0 ιZ0' ιY ιC : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {localizationScale : ℕ → ℕ → ℕ}
    {C237 Calpha5 alpha5 : ℕ → ℕ → ℝ}
    {sourceCard : ∀ t k, σ t k → ℕ}
    {gapCard : ∀ t k, σ t k → ιZ0' t k → ℕ}
    {components : ∀ t k, σ t k → ιZ0' t k → Finset (ιC t k)}
    {componentMetric : ∀ t k, σ t k → ιZ0' t k → ιC t k → ℕ}
    {sourceZ0PrimeIndex : ∀ t k, σ t k → Finset (ιZ0' t k)}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (hC237_nonneg : ∀ t k, 0 ≤ C237 t k)
    (hindex :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          cmp116Eq237Z0PrimeIndex (R t k) Z D P ⊆
            sourceZ0PrimeIndex t k Z)
    (heq237_fixed :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex (R t k) Z D P →
              Finset.sum
                  (cmp116Eq237Z0Fiber (R t k) Z D P Z0')
                  (fun Z0 => (R t k).termWeight Z D P Z0 Z0') ≤
                cmp116Eq229WeightedPWeight
                  (DParts t k)
                  (alpha6 t k)
                  (hp t k).delta
                  (hp t k).kappa
                  (eq229Metric t k)
                  (pResidualWeight t k)
                  Z D P *
                  cmp116Eq237FixedZ0PrimeWeight
                    (hp t k)
                    (localizationScale t k)
                    (C237 t k) (Calpha5 t k) (alpha5 t k)
                    (sourceCard t k) (gapCard t k)
                    (components t k) (componentMetric t k) Z Z0')
    (hpost_eq237 :
      ∀ t k Z,
        Finset.sum (sourceZ0PrimeIndex t k Z) (fun Z0' =>
            cmp116Eq237FixedZ0PrimeWeight
              (hp t k)
              (localizationScale t k)
              (C237 t k) (Calpha5 t k) (alpha5 t k)
              (sourceCard t k) (gapCard t k)
              (components t k) (componentMetric t k) Z Z0') ≤
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2 *
            postPSourceWeight t k Z)
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight
        (fun t k =>
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2))
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  lemma3_activity_estimate
    (of_eq237
      eq229 pStage hC237_nonneg hindex heq237_fixed hpost_eq237
      hmajorization activity)

end CMP116Lemma3WeightedPostPScaleSourceAssumptions

end YangMills.RG
