/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeFluctuationActivity
import YangMills.RG.PhysicalGaugeCMP116Dictionary
import YangMills.RG.BalabanCMP116KsharpAdapter

/-!
# Physical gauge activities to CMP116 raw activity hypotheses

This module is a deliberately thin bridge.  It does not construct the physical
Balaban/CMP116 activity from the gauge-fixed Hessian, and it does not prove
localization of the covariance square root.  Instead it records the exact
transport obligations a source theorem must provide in order to turn the
source-facing physical localized-Gaussian activity certificate into the
CMP116/Appendix-F `hraw` and support hypotheses already consumed downstream.

The nonlocal covariance-root information remains hidden only behind explicit
fields:

* a physical localized-Gaussian activity certificate;
* a CMP116 localized-activity family;
* spectator/fluctuation field transports from CMP116 coordinates to physical
  positive-bond fields;
* exact preservation of `globalEval` under those transports;
* active-support localization inside the Appendix-F skeleton;
* domination of the physical decay weight by the Appendix-F exponential weight.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Finite source-facing adapter from physical positive bonds to the cube-site
layout used by CMP116/Appendix F.

The adapter records only typed coordinate and site transport.  It does not
assert Ω-locality, strong measurability, Gaussian preservation, Wilson-Hessian
identification, or any metric decay estimate. -/
structure PhysicalGaugeCMP116ActivityAdapter
    (I J : Type*) {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (Ψ : Cube d L → Type*) where
  physicalIndex : J → I
  bondToCube : PhysicalBond dPhys N → Cube d L
  spectatorPull :
    ∀ b : PhysicalBond dPhys N, Ψ (bondToCube b) → SUNLieCoord Nc
  fluctuationPull :
    ∀ _ : PhysicalBond dPhys N, (Fin lieDim → ℝ) → SUNLieCoord Nc
  Omega : Finset (Cube d L)

namespace PhysicalGaugeCMP116ActivityAdapter

variable {I J : Type*} {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
variable {Ψ : Cube d L → Type*}

/-- Pull a CMP116 spectator field back to the physical positive-bond field
expected by the physical activity. -/
def pullSpectator
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (ψ : ∀ c : Cube d L, Ψ c) :
    PhysicalGaugeField dPhys N Nc :=
  fun b => A.spectatorPull b (ψ (A.bondToCube b))

/-- Pull a CMP116 fluctuation coordinate field back to the physical
positive-bond field expected by the physical activity. -/
def pullFluctuation
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (φ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    PhysicalGaugeField dPhys N Nc :=
  fun b => A.fluctuationPull b (φ (A.bondToCube b))

/-- Reindex a physical local activity to a cube-indexed CMP116 local activity
using the finite adapter. -/
def activity
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc)
    (X : J) :
    LocalActivity (Cube d L) Ψ (fun _ => Fin lieDim → ℝ) ℂ :=
  (physicalActivity (A.physicalIndex X)).reindex
    A.bondToCube A.spectatorPull A.fluctuationPull

/-- Project a physical active support to the cube support used by CMP116. -/
def activeSupport
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (physicalActiveSupport : I → Finset (PhysicalBond dPhys N))
    (X : J) :
    Finset (Cube d L) :=
  (physicalActiveSupport (A.physicalIndex X)).image A.bondToCube

@[simp] theorem globalEval_activity
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc)
    (X : J)
    (ψ : ∀ c : Cube d L, Ψ c)
    (φ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    (A.activity physicalActivity X).globalEval ψ φ =
      (physicalActivity (A.physicalIndex X)).globalEval
        (A.pullSpectator ψ) (A.pullFluctuation φ) := rfl

@[simp] theorem spectatorSupport_activity
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc)
    (X : J) :
    (A.activity physicalActivity X).spectatorSupport =
      (physicalActivity (A.physicalIndex X)).spectatorSupport.image
        A.bondToCube := rfl

@[simp] theorem fluctuationSupport_activity
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc)
    (X : J) :
    (A.activity physicalActivity X).fluctuationSupport =
      (physicalActivity (A.physicalIndex X)).fluctuationSupport.image
        A.bondToCube := rfl

@[simp] theorem activeSupport_apply
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    (physicalActiveSupport : I → Finset (PhysicalBond dPhys N))
    (X : J) :
    A.activeSupport physicalActiveSupport X =
      (physicalActiveSupport (A.physicalIndex X)).image A.bondToCube := rfl

/-- Physical spectator-support containment transports to the projected
CMP116 active support. -/
theorem spectatorSupport_activity_subset_activeSupport
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    {physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport : I → Finset (PhysicalBond dPhys N)}
    {X : J}
    (h :
      (physicalActivity (A.physicalIndex X)).spectatorSupport ⊆
        physicalActiveSupport (A.physicalIndex X)) :
    (A.activity physicalActivity X).spectatorSupport ⊆
      A.activeSupport physicalActiveSupport X := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨b, hb, rfl⟩
  exact Finset.mem_image.mpr ⟨b, h hb, rfl⟩

/-- Physical fluctuation-support containment transports to the projected
CMP116 active support.  The extra Ω-locality required by CMP116 remains a
separate source obligation. -/
theorem fluctuationSupport_activity_subset_activeSupport
    (A :
      PhysicalGaugeCMP116ActivityAdapter I J (dPhys := dPhys) (N := N)
        (Nc := Nc) (d := d) (L := L) (lieDim := lieDim) Ψ)
    {physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport : I → Finset (PhysicalBond dPhys N)}
    {X : J}
    (h :
      (physicalActivity (A.physicalIndex X)).fluctuationSupport ⊆
        physicalActiveSupport (A.physicalIndex X)) :
    (A.activity physicalActivity X).fluctuationSupport ⊆
      A.activeSupport physicalActiveSupport X := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨b, hb, rfl⟩
  exact Finset.mem_image.mpr ⟨b, h hb, rfl⟩

/-- Canonical finite adapter induced by a physical/CMP116 coordinate
dictionary.  The spectator pull remains source data; the fluctuation pull is
the dictionary's exact scalar-coordinate pullback on each physical bond. -/
noncomputable def ofDictionary
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalIndex : J → I)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc) :
    PhysicalGaugeCMP116ActivityAdapter I J
      (dPhys := dPhys) (N := N) (Nc := Nc)
      (d := d) (L := L) (lieDim := lieDim) Ψ where
  physicalIndex := physicalIndex
  bondToCube := D.siteMap.bondToCube
  spectatorPull := spectatorPull
  fluctuationPull := D.pullFluctuationAtBond
  Omega := D.siteMap.Omega

@[simp] theorem pullFluctuation_ofDictionary
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalIndex : J → I)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (ξ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    (ofDictionary D physicalIndex spectatorPull).pullFluctuation ξ =
      fun b => D.pullFluctuationCochain ξ b := by
  funext b
  exact (D.pullFluctuationCochain_apply ξ b).symm

@[simp] theorem globalEval_activity_ofDictionary
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalIndex : J → I)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc)
    (X : J)
    (ψ : ∀ c : Cube d L, Ψ c)
    (ξ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    ((ofDictionary D physicalIndex spectatorPull).activity
        physicalActivity X).globalEval ψ ξ =
      (physicalActivity (physicalIndex X)).globalEval
        ((ofDictionary D physicalIndex spectatorPull).pullSpectator ψ)
        (fun b => D.pullFluctuationCochain ξ b) := by
  rw [globalEval_activity, pullFluctuation_ofDictionary]
  simp [ofDictionary]

theorem spectatorSupport_activity_ofDictionary_subset_iff
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalIndex : J → I)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc)
    (X : J) (Y : Finset (Cube d L)) :
    ((ofDictionary D physicalIndex spectatorPull).activity
        physicalActivity X).spectatorSupport ⊆ Y ↔
      (physicalActivity (physicalIndex X)).spectatorSupport ⊆
        D.physicalBondsOfCells Y := by
  simpa [ofDictionary] using
    D.image_bondToCube_subset_iff_physicalBondsOfCells
      ((physicalActivity (physicalIndex X)).spectatorSupport) Y

theorem fluctuationSupport_activity_ofDictionary_subset_iff
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalIndex : J → I)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (physicalActivity : I → PhysicalGaugeLocalActivity dPhys N Nc)
    (X : J) (Y : Finset (Cube d L)) :
    ((ofDictionary D physicalIndex spectatorPull).activity
        physicalActivity X).fluctuationSupport ⊆ Y ↔
      (physicalActivity (physicalIndex X)).fluctuationSupport ⊆
        D.physicalBondsOfCells Y := by
  simpa [ofDictionary] using
    D.image_bondToCube_subset_iff_physicalBondsOfCells
      ((physicalActivity (physicalIndex X)).fluctuationSupport) Y

theorem activeSupport_ofDictionary_subset_iff
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalIndex : J → I)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (physicalActiveSupport : I → Finset (PhysicalBond dPhys N))
    (X : J) (Y : Finset (Cube d L)) :
    (ofDictionary D physicalIndex spectatorPull).activeSupport
        physicalActiveSupport X ⊆ Y ↔
      physicalActiveSupport (physicalIndex X) ⊆
        D.physicalBondsOfCells Y := by
  simpa [ofDictionary, activeSupport] using
    D.image_bondToCube_subset_iff_physicalBondsOfCells
      (physicalActiveSupport (physicalIndex X)) Y

end PhysicalGaugeCMP116ActivityAdapter

/-- Universal CMP116 first-activity raw metric decay over an Appendix-F
polymer family.

This is the raw `H(X)` bound consumed by the first localized activity/K# layer.
It is not the second-Ursell `H#` residual estimate. -/
def BalabanCMP116RawMetricDecay
    {d L : ℕ} [NeZero L]
    {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (H0 κ : ℝ) : Prop :=
  ∀ (ψ : ∀ b : Cube d L, Ψ b)
    (φ : ∀ _ : Cube d L, Fin lieDim → ℝ)
    X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H0 * appendixFHoleExpWeight HF κ X.val

/-- Source-facing transport package from a physical localized Gaussian activity
certificate to a CMP116 localized activity family.

All analytic and geometric content is explicit data here.  A future source
theorem has to instantiate this record by identifying the CMP116 local
activity with the physical fluctuation integral after the change of variables
`B' = C^{1/2} X`, proving the support localization, and supplying the weight
domination. -/
structure PhysicalGaugeCMP116ActivityTransport
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (covNormBound rootNormBound : ℝ)
    (covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N))
    (amplitude weight : OmegaPolymerType HF z → ℝ)
    (H0 κ : ℝ)
    (sourceConstruction : Prop) where
  certificate :
    PhysicalLocalizedGaussianActivityCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight physicalActivity physicalActiveSupport amplitude weight H0
      sourceConstruction
  family :
    BalabanCMP116LocalizedActivityFamily
      (Cube d L) lieDim Ψ (OmegaPolymerType HF z)
  spectatorTransport :
    (∀ b : Cube d L, Ψ b) → PhysicalGaugeField dPhys N Nc
  fluctuationTransport :
    (∀ _ : Cube d L, Fin lieDim → Real) → PhysicalGaugeField dPhys N Nc
  globalEval_eq :
    ∀ X ψ φ,
      (family.activity X).globalEval ψ φ =
        (physicalActivity X).globalEval
          (spectatorTransport ψ) (fluctuationTransport φ)
  activeSupport_subset_skeleton :
    ∀ X, X ∈ Λ → family.activeSupport X ⊆ skeleton HF X.val
  weight_domination :
    ∀ X, X ∈ Λ → weight X ≤ appendixFHoleExpWeight HF κ X.val

namespace BalabanCMP116LocalizedActivityFamily

/-- Extract the CMP116 localized family carried by a physical/CMP116 transport
package.

This is intentionally a projection from the full transport package.  It is not
a derivation from the physical certificate or from covariance localization
alone: the package already contains the CMP116 family, its measurability, and
its support fields. -/
def of_physicalLocalizedGaussianActivityCertificate
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction) :
    BalabanCMP116LocalizedActivityFamily
      (Cube d L) lieDim Ψ (OmegaPolymerType HF z) :=
  T.family

end BalabanCMP116LocalizedActivityFamily

/-- The source transport package immediately supplies the CMP116 Appendix-F
support hypotheses. -/
theorem physicalGaugeCMP116SupportHypotheses_of_transport
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction) :
    BalabanCMP116AppendixFSupportHypotheses
      (lieDim := lieDim) (Ψ := Ψ) HF z Λ T.family := by
  exact
    BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_subset_skeleton
      T.activeSupport_subset_skeleton

/-- Transport a physical raw-decay estimate through the exact physical/CMP116
field dictionary to the named CMP116 raw metric-decay predicate. -/
theorem balabanCMP116RawMetricDecay_of_physicalGaugeRawActivityDecay
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction)
    (hphysical :
      PhysicalGaugeRawActivityDecay physicalActivity weight H0)
    (hH0 : 0 ≤ H0) :
    BalabanCMP116RawMetricDecay HF z Λ T.family H0 κ := by
  intro ψ φ X hX
  calc
    ‖(T.family.activity X).globalEval ψ φ‖ =
        ‖(physicalActivity X).globalEval
          (T.spectatorTransport ψ) (T.fluctuationTransport φ)‖ := by
      rw [T.globalEval_eq X ψ φ]
    _ ≤ H0 * weight X :=
      hphysical X (T.spectatorTransport ψ) (T.fluctuationTransport φ)
    _ ≤ H0 * appendixFHoleExpWeight HF κ X.val :=
      mul_le_mul_of_nonneg_left (T.weight_domination X hX) hH0

/-- The source transport package converts the physical localized-Gaussian
raw-decay estimate into the CMP116 `hraw` shape consumed by Appendix F. -/
theorem balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction)
    (hH0 : 0 ≤ H0) :
    ∀ (ψ : ∀ b : Cube d L, Ψ b)
      (φ : ∀ _ : Cube d L, Fin lieDim → Real) X, X ∈ Λ →
      ‖(T.family.activity X).globalEval ψ φ‖ ≤
        H0 * appendixFHoleExpWeight HF κ X.val := by
  exact
    balabanCMP116RawMetricDecay_of_physicalGaugeRawActivityDecay T
      (physicalGaugeRawActivityDecay_of_localizedGaussianActivityCertificate
        T.certificate)
      hH0

end YangMills.RG
