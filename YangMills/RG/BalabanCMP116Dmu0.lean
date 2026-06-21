/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.GaussianPi
import YangMills.RG.UltralocalFactorization

/-!
# Balaban CMP116: the product Gaussian `dmu0`

Balaban, CMP 116 (1988), equations (2.5)--(2.6), conditions the covariance
Gaussian fluctuation integral on a localization domain and makes the linear
change `B' = (C^(k))^(1/2) X`.  The displayed post-change measure is a product
of standard finite-dimensional Gaussians over bonds.

This file formalizes only that finite product-measure substrate.  The
nonlocality now lives in the transformed integrand through `C^(k)`, its square
root, and the localized random-walk expansion; the support/decay constants that
turn Balaban's localized `H(Z)` into the Appendix-F hypotheses remain explicit
source obligations elsewhere.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open MeasureTheory ProbabilityTheory

namespace YangMills.RG

open scoped BigOperators

/-- The standard Gaussian measure on one Lie-algebra bond coordinate block,
modeled as `Fin lieDim -> Real`. -/
noncomputable def balabanCMP116BondGaussian (lieDim : Nat) :
    Measure (Fin lieDim -> Real) :=
  Measure.pi fun _ : Fin lieDim => gaussianReal 0 (1 : NNReal)

/-- The per-bond standard Gaussian is a probability measure. -/
theorem balabanCMP116BondGaussian_isProbability (lieDim : Nat) :
    IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) := by
  unfold balabanCMP116BondGaussian
  infer_instance

/-- The per-bond standard Gaussian is Gaussian in Mathlib's sense. -/
theorem balabanCMP116BondGaussian_isGaussian (lieDim : Nat) :
    IsGaussian (balabanCMP116BondGaussian lieDim) := by
  simpa [balabanCMP116BondGaussian] using
    (isGaussian_pi (fun _ : Fin lieDim => (0 : Real))
      (fun _ : Fin lieDim => (1 : NNReal)))

/-- CMP116's `dmu0`: the ultralocal product over bonds of the standard
finite-dimensional Gaussian in the `X(b)` variables. -/
noncomputable def balabanCMP116Dmu0 (Bond : Type*) [Fintype Bond] (lieDim : Nat) :
    Measure (Bond -> Fin lieDim -> Real) :=
  Measure.pi fun _ : Bond => balabanCMP116BondGaussian lieDim

/-- The CMP116 product measure is a probability measure. -/
theorem balabanCMP116Dmu0_isProbability
    (Bond : Type*) [Fintype Bond] (lieDim : Nat) :
    IsProbabilityMeasure (balabanCMP116Dmu0 Bond lieDim) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  unfold balabanCMP116Dmu0
  infer_instance

/-- A flattened version of the same standard product Gaussian over
bond-coordinate pairs.  This matches the literal product over bonds and Lie
coordinates in the source formula, while `balabanCMP116Dmu0` is shaped for the
type-local `LocalActivity` API. -/
noncomputable def balabanCMP116Dmu0Flat
    (Bond : Type*) [Fintype Bond] (lieDim : Nat) :
    Measure (Bond × Fin lieDim -> Real) :=
  Measure.pi fun _ : Bond × Fin lieDim => gaussianReal 0 (1 : NNReal)

/-- The flattened product measure is Gaussian in Mathlib's sense. -/
theorem balabanCMP116Dmu0Flat_isGaussian
    (Bond : Type*) [Fintype Bond] (lieDim : Nat) :
    IsGaussian (balabanCMP116Dmu0Flat Bond lieDim) := by
  simpa [balabanCMP116Dmu0Flat] using
    (isGaussian_pi (fun _ : Bond × Fin lieDim => (0 : Real))
      (fun _ : Bond × Fin lieDim => (1 : NNReal)))

/-- The flattened product measure is a probability measure. -/
theorem balabanCMP116Dmu0Flat_isProbability
    (Bond : Type*) [Fintype Bond] (lieDim : Nat) :
    IsProbabilityMeasure (balabanCMP116Dmu0Flat Bond lieDim) := by
  unfold balabanCMP116Dmu0Flat
  infer_instance

/-- Disjoint local functionals factor under the CMP116 `dmu0` product measure. -/
theorem balabanCMP116Dmu0_integral_mul_of_disjoint_support
    {Bond : Type*} [Fintype Bond] [DecidableEq Bond]
    (lieDim : Nat)
    (F G : LocalFunctional Bond (fun _ => Fin lieDim -> Real) Complex)
    (hdisj : Disjoint F.support G.support) :
    ∫ X, F.globalEval X * G.globalEval X ∂(balabanCMP116Dmu0 Bond lieDim)
      =
      (∫ X, F.globalEval X ∂(balabanCMP116Dmu0 Bond lieDim)) *
        ∫ X, G.globalEval X ∂(balabanCMP116Dmu0 Bond lieDim) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116Dmu0] using
    (LocalFunctional.integral_mul_of_disjoint_support
      (Site := Bond) (β := Fin lieDim -> Real)
      (μ := balabanCMP116BondGaussian lieDim)
      (F := F) (G := G) hdisj)

/-- A finite product of local functionals with pairwise-disjoint supports
factorizes under the CMP116 `dmu0` product measure. -/
theorem balabanCMP116Dmu0_integral_finsetProd_of_pairwise_disjoint_support
    {Bond ι : Type*} [Fintype Bond] [DecidableEq Bond] [DecidableEq ι]
    (lieDim : Nat)
    (I : Finset ι)
    (F : ι -> LocalFunctional Bond (fun _ => Fin lieDim -> Real) Complex)
    (hpair : ∀ i, i ∈ I -> ∀ j, j ∈ I -> i ≠ j ->
      Disjoint (F i).support (F j).support) :
    ∫ X, (LocalFunctional.finsetProd I F).globalEval X
        ∂(balabanCMP116Dmu0 Bond lieDim)
      =
      ∏ i ∈ I,
        ∫ X, (F i).globalEval X
          ∂(balabanCMP116Dmu0 Bond lieDim) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116Dmu0] using
    (LocalFunctional.integral_finsetProd_of_pairwise_disjoint_support
      (Site := Bond) (β := Fin lieDim -> Real)
      (μ := balabanCMP116BondGaussian lieDim)
      (I := I) (F := F) hpair)

/-- For fixed spectator fields, disjoint local activities factor under the
CMP116 `dmu0` product fluctuation measure. -/
theorem balabanCMP116Dmu0_integral_mul_of_disjoint_fluctuationSupport
    {Bond : Type*} [Fintype Bond] [DecidableEq Bond]
    (lieDim : Nat) {Psi : Bond -> Type*}
    (F G : LocalActivity Bond Psi (fun _ => Fin lieDim -> Real) Complex)
    (psi : ∀ b, Psi b)
    (hdisj : Disjoint F.fluctuationSupport G.fluctuationSupport) :
    ∫ X, F.globalEval psi X * G.globalEval psi X
        ∂(balabanCMP116Dmu0 Bond lieDim)
      =
      (∫ X, F.globalEval psi X ∂(balabanCMP116Dmu0 Bond lieDim)) *
        ∫ X, G.globalEval psi X ∂(balabanCMP116Dmu0 Bond lieDim) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116Dmu0] using
    (LocalActivity.integral_mul_of_disjoint_fluctuationSupport
      (Site := Bond) (β := Fin lieDim -> Real)
      (μ := balabanCMP116BondGaussian lieDim)
      (F := F) (G := G) (ψ := psi) hdisj)

/-- For fixed spectator fields, a finite product of local activities with
pairwise-disjoint fluctuation supports factorizes under the CMP116 `dmu0`
product measure. -/
theorem balabanCMP116Dmu0_integral_finsetProd_of_pairwise_disjoint_fluctuationSupport
    {Bond ι : Type*} [Fintype Bond] [DecidableEq Bond] [DecidableEq ι]
    (lieDim : Nat) {Psi : Bond -> Type*}
    (I : Finset ι)
    (F : ι -> LocalActivity Bond Psi (fun _ => Fin lieDim -> Real) Complex)
    (psi : ∀ b, Psi b)
    (hpair : ∀ i, i ∈ I -> ∀ j, j ∈ I -> i ≠ j ->
      Disjoint (F i).fluctuationSupport (F j).fluctuationSupport) :
    ∫ X, (LocalActivity.finsetProd I F).globalEval psi X
        ∂(balabanCMP116Dmu0 Bond lieDim)
      =
      ∏ i ∈ I,
        ∫ X, (F i).globalEval psi X
          ∂(balabanCMP116Dmu0 Bond lieDim) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116Dmu0] using
    (LocalActivity.integral_finsetProd_of_pairwise_disjoint_fluctuationSupport
      (Site := Bond) (β := Fin lieDim -> Real)
      (μ := balabanCMP116BondGaussian lieDim)
      (I := I) (F := F) (ψ := psi) hpair)

end YangMills.RG
