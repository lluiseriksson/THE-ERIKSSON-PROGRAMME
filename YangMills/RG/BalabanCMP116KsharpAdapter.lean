/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Localization
import YangMills.RG.AppendixFCluster3Geometry
import YangMills.RG.AppendixFKsharpEstimate

/-!
# Balaban CMP116 to Appendix-F `K#`

This module specializes the first Appendix-F connected-activity compiler to the
CMP116 localized activity package.  The product fluctuation measure is the
source-shaped `dmu0`; the only remaining support input is the promised
localization theorem saying that each Balaban active support is contained in
the full Appendix-F polymer, and, for the skeleton consumers, in its active
hole skeleton.

No estimate from Balaban's random-walk expansion is proved here.  The raw
pointwise decay, integrability, and support localization statements remain
explicit hypotheses.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-- The source-localization obligation needed to feed a CMP116 localized
family into the source-facing Appendix-F hole compiler.

The source theorem only has to prove active-skeleton localization.  The
full-support statement used by target-union bookkeeping follows formally from
`skeleton_subset`; it is not a separate Balaban/CMP116 obligation. -/
structure BalabanCMP116AppendixFSupportHypotheses
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z)) : Prop where
  activeSupport_subset_skeleton :
    ∀ X, X ∈ Λ → F.activeSupport X ⊆ skeleton HF X.val

namespace BalabanCMP116AppendixFSupportHypotheses

variable {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
variable {HF : HoleFamily d L} {z : Finset (Cube d L) → ℂ}
variable {Λ : Finset (OmegaPolymerType HF z)}
variable {F :
  BalabanCMP116LocalizedActivityFamily
    (Cube d L) lieDim Ψ (OmegaPolymerType HF z)}

/-- Full-target localization follows from active-skeleton localization and the
finite set-theoretic fact `skeleton HF X ⊆ X`. -/
theorem activeSupport_subset_full
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → F.activeSupport X ⊆ X.val := by
  intro X hX x hx
  exact skeleton_subset HF X.val (h.activeSupport_subset_skeleton X hX hx)

/-- A source theorem that localizes every CMP116 active support inside the
active skeleton automatically supplies both Appendix-F support hypotheses.

This is the intended bridge for the CMP116 random-walk localization statement:
once the printed construction proves `F.activeSupport X ⊆ skeleton HF X.val`,
the full-target inclusion follows by `skeleton_subset`. -/
theorem of_activeSupport_subset_skeleton
    (hskel : ∀ X, X ∈ Λ → F.activeSupport X ⊆ skeleton HF X.val) :
    BalabanCMP116AppendixFSupportHypotheses HF z Λ F where
  activeSupport_subset_skeleton := hskel

/-- Equality with the active skeleton is a convenient source-facing way to
build the CMP116 Appendix-F support package. -/
theorem of_activeSupport_eq_skeleton
    (hskel : ∀ X, X ∈ Λ → F.activeSupport X = skeleton HF X.val) :
    BalabanCMP116AppendixFSupportHypotheses HF z Λ F :=
  of_activeSupport_subset_skeleton
    (fun X hX => by
      rw [hskel X hX])

/-- If the source describes each active support as lying in the full target
polymer intersected with the active region `HF.omegaRegion`, it supplies the
Lean skeleton-locality field.

This is the common source form matching
`skeleton HF X.val = X.val ∩ HF.omegaRegion`; it is still only finite set
bookkeeping, not the missing CMP116 localization theorem. -/
theorem of_activeSupport_subset_target_inter_omegaRegion
    (hOmega : F.Omega = HF.omegaRegion)
    (hactive : ∀ X, X ∈ Λ → F.activeSupport X ⊆ X.val ∩ F.Omega) :
    BalabanCMP116AppendixFSupportHypotheses HF z Λ F :=
  of_activeSupport_subset_skeleton
    (fun X hX => by
      have hsub : F.activeSupport X ⊆ X.val ∩ HF.omegaRegion := by
        simpa [hOmega] using hactive X hX
      simpa [skeleton_eq_inter_omegaRegion] using hsub)

/-- Equality with `X ∩ HF.omegaRegion` is a convenient source-facing way to
build the CMP116 Appendix-F support package.

The source theorem may identify the localized active domain with the target
polymer clipped to the active region; Lean then rewrites that region to the
existing skeleton. -/
theorem of_activeSupport_eq_target_inter_omegaRegion
    (hOmega : F.Omega = HF.omegaRegion)
    (hactive : ∀ X, X ∈ Λ → F.activeSupport X = X.val ∩ F.Omega) :
    BalabanCMP116AppendixFSupportHypotheses HF z Λ F :=
  of_activeSupport_subset_target_inter_omegaRegion hOmega
    (fun X hX => by
      rw [hactive X hX])

/-- The inclusion-form clipped active region is enough for the one-way
hard-core graph implication: if CMP116's `zeta` detects an active-support
overlap, then the corresponding Appendix-F active skeletons overlap.

The reverse implication needs equality, not just inclusion. -/
theorem zeta_eq_zero_imp_not_disjoint_skeleton_of_activeSupport_subset_target_inter_omegaRegion
    (hOmega : F.Omega = HF.omegaRegion)
    (hactive : ∀ X, X ∈ Λ → F.activeSupport X ⊆ X.val ∩ F.Omega)
    {X Y : OmegaPolymerType HF z} (hX : X ∈ Λ) (hY : Y ∈ Λ) :
    F.zeta X Y = 0 → ¬ Disjoint (skeleton HF X.val) (skeleton HF Y.val) := by
  intro hzeta hdisj
  have hactiveOverlap :
      ¬ Disjoint (F.Omega ∩ F.activeSupport X) (F.Omega ∩ F.activeSupport Y) := by
    simpa [BalabanCMP116LocalizedActivityFamily.zeta] using
      (balabanCMP116HardCoreZeta_eq_zero_iff F.Omega F.activeSupport X Y).mp hzeta
  apply hactiveOverlap
  rw [Finset.disjoint_left] at hdisj ⊢
  intro x hxX hxY
  have hxXactive : x ∈ F.activeSupport X := (Finset.mem_inter.mp hxX).2
  have hxYactive : x ∈ F.activeSupport Y := (Finset.mem_inter.mp hxY).2
  have hxXskel : x ∈ skeleton HF X.val := by
    have hx : x ∈ X.val ∩ HF.omegaRegion := by
      simpa [hOmega] using hactive X hX hxXactive
    simpa [skeleton_eq_inter_omegaRegion] using hx
  have hxYskel : x ∈ skeleton HF Y.val := by
    have hy : x ∈ Y.val ∩ HF.omegaRegion := by
      simpa [hOmega] using hactive Y hY hxYactive
    simpa [skeleton_eq_inter_omegaRegion] using hy
  exact hdisj hxXskel hxYskel

/-- With only inclusion into the clipped active region, CMP116 Ω-overlap edges
still map into Appendix-F skeleton-overlap edges. -/
theorem omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_activeSupport_subset_target_inter_omegaRegion
    (hOmega : F.Omega = HF.omegaRegion)
    (hactive : ∀ X, X ∈ Λ → F.activeSupport X ⊆ X.val ∩ F.Omega)
    {X Y : OmegaPolymerType HF z} (hX : X ∈ Λ) (hY : Y ∈ Λ) :
    F.omegaGraph.Adj X Y →
      (omegaOverlapGraph (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)).Adj X Y := by
  intro hAdj
  have hcmp := (BalabanCMP116LocalizedActivityFamily.omegaGraph_adj_iff_zeta_eq_zero
    F X Y).mp hAdj
  have hskel :
      ¬ Disjoint (skeleton HF X.val) (skeleton HF Y.val) :=
    zeta_eq_zero_imp_not_disjoint_skeleton_of_activeSupport_subset_target_inter_omegaRegion
      hOmega hactive hX hY hcmp.2
  rw [omegaOverlapGraph_adj_iff]
  exact ⟨hcmp.1, by simpa using hskel⟩

/-- Under the clipped-active-region identification, the CMP116 hard-core
function `zeta` vanishes exactly when the two Appendix-F active skeletons
overlap.

This is still finite support bookkeeping: it only rewrites
`F.Omega ∩ F.activeSupport X` to `skeleton HF X.val`. -/
theorem zeta_eq_zero_iff_not_disjoint_skeleton_of_activeSupport_eq_target_inter_omegaRegion
    (hOmega : F.Omega = HF.omegaRegion)
    (hactive : ∀ X, X ∈ Λ → F.activeSupport X = X.val ∩ F.Omega)
    {X Y : OmegaPolymerType HF z} (hX : X ∈ Λ) (hY : Y ∈ Λ) :
    F.zeta X Y = 0 ↔ ¬ Disjoint (skeleton HF X.val) (skeleton HF Y.val) := by
  have hFX : F.Omega ∩ F.activeSupport X = skeleton HF X.val := by
    rw [hactive X hX, hOmega]
    simp [skeleton_eq_inter_omegaRegion, Finset.inter_left_comm]
  have hFY : F.Omega ∩ F.activeSupport Y = skeleton HF Y.val := by
    rw [hactive Y hY, hOmega]
    simp [skeleton_eq_inter_omegaRegion, Finset.inter_left_comm]
  simpa [BalabanCMP116LocalizedActivityFamily.zeta, hFX, hFY] using
    (balabanCMP116HardCoreZeta_eq_zero_iff F.Omega F.activeSupport X Y)

/-- Under the clipped-active-region identification, the CMP116 Ω-overlap graph
is the same adjacency relation as the Appendix-F skeleton-overlap graph on the
polymers present in `Λ`. -/
theorem omegaGraph_adj_iff_skeletonOverlapGraph_adj_of_activeSupport_eq_target_inter_omegaRegion
    (hOmega : F.Omega = HF.omegaRegion)
    (hactive : ∀ X, X ∈ Λ → F.activeSupport X = X.val ∩ F.Omega)
    {X Y : OmegaPolymerType HF z} (hX : X ∈ Λ) (hY : Y ∈ Λ) :
    F.omegaGraph.Adj X Y ↔
      (omegaOverlapGraph (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)).Adj X Y := by
  have hFX : F.Omega ∩ F.activeSupport X = skeleton HF X.val := by
    rw [hactive X hX, hOmega]
    simp [skeleton_eq_inter_omegaRegion, Finset.inter_left_comm]
  have hFY : F.Omega ∩ F.activeSupport Y = skeleton HF Y.val := by
    rw [hactive Y hY, hOmega]
    simp [skeleton_eq_inter_omegaRegion, Finset.inter_left_comm]
  rw [BalabanCMP116LocalizedActivityFamily.omegaGraph,
    omegaOverlapGraph_adj_iff, omegaOverlapGraph_adj_iff]
  simp [hFX, hFY]

/-- CMP116 spectator locality, converted to the full Appendix-F target support. -/
theorem spectatorSupport_subset_full
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).spectatorSupport ⊆ X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_full X hX (F.spectatorSupport_subset X hx)

/-- CMP116 fluctuation locality, converted to the full Appendix-F target
support. -/
theorem fluctuationSupport_subset_full
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).fluctuationSupport ⊆ X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_full X hX
    ((Finset.mem_inter.mp (F.fluctuationSupport_subset X hx)).2)

/-- CMP116 spectator locality, converted to the Appendix-F active skeleton. -/
theorem spectatorSupport_subset_skeleton
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).spectatorSupport ⊆ skeleton HF X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_skeleton X hX (F.spectatorSupport_subset X hx)

/-- CMP116 fluctuation locality, converted to the Appendix-F active skeleton. -/
theorem fluctuationSupport_subset_skeleton
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    ∀ X, X ∈ Λ → (F.activity X).fluctuationSupport ⊆ skeleton HF X.val := by
  intro X hX x hx
  exact h.activeSupport_subset_skeleton X hX
    ((Finset.mem_inter.mp (F.fluctuationSupport_subset X hx)).2)

end BalabanCMP116AppendixFSupportHypotheses

/-- The CMP116-specialized first connected Appendix-F local activity. -/
noncomputable def balabanCMP116AppendixFConnectedLocalActivity
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L)) :
    LocalActivity (Cube d L) Ψ (fun _ => Fin lieDim -> Real) ℂ :=
  appendixFHoleConnectedLocalActivity HF z Λ F.activity Y

/-- The CMP116-specialized first integrated activity `K#`, using the
source-shaped product fluctuation measure `dmu0`. -/
noncomputable def balabanCMP116AppendixFKsharp
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L)) :
    LocalFunctional (Cube d L) Ψ ℂ :=
  appendixFHoleKsharp HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y

@[simp] theorem balabanCMP116AppendixFConnectedLocalActivity_globalEval
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x)
    (φ : ∀ _ : Cube d L, Fin lieDim -> Real) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ =
      appendixFHoleConnectedMayerActivity HF z Λ
        (fun X => Complex.exp ((F.activity X).globalEval ψ φ) - 1) Y := by
  simp [balabanCMP116AppendixFConnectedLocalActivity]

/-- Structural measurability of the CMP116 connected first activity from
factorwise measurability of the localized raw activities. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_globalEval_stronglyMeasurable
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x)
    (hmeas : ∀ X, X ∈ Λ →
      StronglyMeasurable
        (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
          (F.activity X).globalEval ψ φ)) :
    StronglyMeasurable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity
          HF z Λ F Y).globalEval ψ φ) := by
  simpa [balabanCMP116AppendixFConnectedLocalActivity] using
    (appendixFHoleConnectedLocalActivity_globalEval_stronglyMeasurable
      HF z Λ F.activity Y ψ hmeas)

/-- Structural measurability of the CMP116 connected first activity, using the
measurability field carried by the localized source package itself. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_globalEval_stronglyMeasurable_of_source
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) :
    StronglyMeasurable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity
          HF z Λ F Y).globalEval ψ φ) :=
  balabanCMP116AppendixFConnectedLocalActivity_globalEval_stronglyMeasurable
    HF z Λ F Y ψ
    (fun X _hX =>
      BalabanCMP116LocalizedActivityFamily.activity_globalEval_stronglyMeasurable
        F X ψ)

@[simp] theorem balabanCMP116AppendixFKsharp_globalEval
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ =
      ∫ φ : (∀ _ : Cube d L, Fin lieDim -> Real),
        (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) := by
  rfl

/-- Direct raw-Mayer integral form of the CMP116-specialized `K#`. -/
theorem balabanCMP116AppendixFKsharp_globalEval_eq_integral_connectedMayerActivity
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ =
      ∫ φ : (∀ _ : Cube d L, Fin lieDim -> Real),
        appendixFHoleConnectedMayerActivity HF z Λ
          (fun X => Complex.exp ((F.activity X).globalEval ψ φ) - 1) Y
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) := by
  rw [balabanCMP116AppendixFKsharp, balabanCMP116Dmu0]
  exact appendixFHoleKsharp_globalEval_eq_integral_connectedMayerActivity
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y ψ

/-- Full-support locality for the CMP116-specialized connected activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_spectatorSupport_subset
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).spectatorSupport ⊆ Y := by
  exact appendixFHoleConnectedLocalActivity_spectatorSupport_subset
    HF z Λ F.activity Y h.spectatorSupport_subset_full

/-- Full-support fluctuation locality for the CMP116-specialized connected
activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_fluctuationSupport_subset
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).fluctuationSupport ⊆ Y := by
  exact appendixFHoleConnectedLocalActivity_fluctuationSupport_subset
    HF z Λ F.activity Y h.fluctuationSupport_subset_full

/-- Active-skeleton spectator locality for the CMP116-specialized connected
activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_spectatorSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).spectatorSupport ⊆
      skeleton HF Y := by
  exact appendixFHoleConnectedLocalActivity_spectatorSupport_subset_skeleton
    HF z Λ F.activity Y h.spectatorSupport_subset_skeleton

/-- Active-skeleton fluctuation locality for the CMP116-specialized connected
activity. -/
theorem balabanCMP116AppendixFConnectedLocalActivity_fluctuationSupport_subset_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).fluctuationSupport ⊆
      skeleton HF Y := by
  exact appendixFHoleConnectedLocalActivity_fluctuationSupport_subset_skeleton
    HF z Λ F.activity Y h.fluctuationSupport_subset_skeleton

/-- Full-target support for the CMP116-specialized `K#`. -/
theorem balabanCMP116AppendixFKsharp_support_subset
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).support ⊆ Y := by
  exact appendixFHoleKsharp_support_subset
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y
    h.spectatorSupport_subset_full

/-- Active-skeleton support for the CMP116-specialized `K#`. -/
theorem balabanCMP116AppendixFKsharp_support_subset_skeleton
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (Y : Finset (Cube d L))
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F) :
    (balabanCMP116AppendixFKsharp HF z Λ F Y).support ⊆ skeleton HF Y := by
  exact appendixFHoleKsharp_support_subset_skeleton
    HF z Λ F.activity (balabanCMP116BondGaussian lieDim) Y
    h.spectatorSupport_subset_skeleton

/-- The finite target-family first-integration identity, specialized to the
CMP116 product Gaussian. -/
theorem integral_sum_balabanCMP116AppendixFConnectedLocalActivity_eq_sum_prod_Ksharp
    {d L : ℕ} [NeZero L] {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    (ψ : ∀ x, Ψ x)
    (h : BalabanCMP116AppendixFSupportHypotheses HF z Λ F)
    (hint : ∀ targets,
      targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ →
        Integrable
          (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
            ∏ Y ∈ targets,
              (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ)
          (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ∫ φ : (∀ _ : Cube d L, Fin lieDim -> Real),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ)
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim)
      =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          (balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116AppendixFConnectedLocalActivity,
    balabanCMP116AppendixFKsharp, balabanCMP116Dmu0] using
    (integral_sum_appendixFHoleConnectedLocalActivity_eq_sum_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) ψ
      h.fluctuationSupport_subset_skeleton
      (by
        intro targets htargets
        simpa [balabanCMP116AppendixFConnectedLocalActivity,
          balabanCMP116Dmu0] using hint targets htargets))

/-- Source-shaped rooted first-activity estimate, specialized to CMP116
`dmu0`.  The raw pointwise decay and integrability hypotheses are exactly the
analytic/source obligations still missing from the Yang-Mills RG input. -/
theorem norm_balabanCMP116AppendixFKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ)
      (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ‖(balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ‖
      ≤
    appendixFHoleExpWeight HF (κ - κ₀) Y *
      (Real.exp
        (2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116AppendixFKsharp] using
    (norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) hY ψ
      hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw
      (by
        simpa [balabanCMP116AppendixFConnectedLocalActivity,
          balabanCMP116Dmu0] using hint))

/-- Linearized source-shaped rooted first-activity estimate, specialized to
CMP116 `dmu0`.

This is the CMP116 wrapper around
`norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted`;
the raw pointwise decay and fluctuation-integrability hypotheses remain the
source obligations. -/
theorem norm_balabanCMP116AppendixFKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hsmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity HF z Λ F Y).globalEval ψ φ)
      (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    ‖(balabanCMP116AppendixFKsharp HF z Λ F Y).globalEval ψ‖ ≤
      (2 * H₀ * K₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116AppendixFKsharp] using
    (norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) hY ψ
      hH₀ hH₀_one hK₀ hsmall hκ₀ hκ hroot hraw
      (by
        simpa [balabanCMP116AppendixFConnectedLocalActivity,
          balabanCMP116Dmu0] using hint))

/-- CMP116 source-shaped compiler for the first connected-activity
integrability obligation.

The analytic input is now strong measurability of the connected integrand.
The verified finite Appendix-F bound, fed by the raw pointwise metric decay and
rooted summability, supplies the a.e. boundedness needed for integrability under
the product Gaussian `dmu0`. -/
theorem integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hmeas :
      AEStronglyMeasurable
        (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
          (balabanCMP116AppendixFConnectedLocalActivity
            HF z Λ F Y).globalEval ψ φ)
        (balabanCMP116Dmu0 (Cube d L) lieDim)) :
    Integrable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity
          HF z Λ F Y).globalEval ψ φ)
      (balabanCMP116Dmu0 (Cube d L) lieDim) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116AppendixFConnectedLocalActivity, balabanCMP116Dmu0] using
    (integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_rooted
      HF z Λ F.activity (balabanCMP116BondGaussian lieDim) hY ψ
      hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw
      (by
        simpa [balabanCMP116AppendixFConnectedLocalActivity,
          balabanCMP116Dmu0] using hmeas))

/-- Ordinary strong measurability form of the CMP116 source-shaped
integrability compiler for the first connected Appendix-F activity. -/
theorem integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_stronglyMeasurable
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hmeas :
      StronglyMeasurable
        (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
          (balabanCMP116AppendixFConnectedLocalActivity
            HF z Λ F Y).globalEval ψ φ)) :
    Integrable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity
          HF z Λ F Y).globalEval ψ φ)
      (balabanCMP116Dmu0 (Cube d L) lieDim) :=
  integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted
    HF z Λ F hY ψ hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw
    hmeas.aestronglyMeasurable

/-- Factorwise strong measurability form of the CMP116 source-shaped
integrability compiler.  This is the source-facing shape for CMP116
localization: each localized raw activity is strongly measurable, and the
finite Appendix-F connected-cover compiler constructs the connected
integrand's measurability. -/
theorem integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_factor_stronglyMeasurable
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hmeas : ∀ X, X ∈ Λ →
      StronglyMeasurable
        (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
          (F.activity X).globalEval ψ φ)) :
    Integrable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity
          HF z Λ F Y).globalEval ψ φ)
      (balabanCMP116Dmu0 (Cube d L) lieDim) :=
  integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_stronglyMeasurable
    HF z Λ F hY ψ hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw
    (balabanCMP116AppendixFConnectedLocalActivity_globalEval_stronglyMeasurable
      HF z Λ F Y ψ hmeas)

/-- Source-package form of the CMP116 rooted integrability compiler.

Here the only remaining analytic estimate is the raw metric-decay bound
`hraw`; measurability is supplied by `BalabanCMP116LocalizedActivityFamily`
itself. -/
theorem integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_source
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (F :
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim Ψ (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(F.activity X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val) :
    Integrable
      (fun φ : (∀ _ : Cube d L, Fin lieDim -> Real) =>
        (balabanCMP116AppendixFConnectedLocalActivity
          HF z Λ F Y).globalEval ψ φ)
      (balabanCMP116Dmu0 (Cube d L) lieDim) :=
  integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_factor_stronglyMeasurable
    HF z Λ F hY ψ hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw
    (fun X _hX =>
      BalabanCMP116LocalizedActivityFamily.activity_globalEval_stronglyMeasurable
        F X ψ)

end YangMills.RG
