/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellMarkedFugacity
import YangMills.RG.BalabanCMP116HsharpSource

/-!
# Source-facing marked-vertex contracts for Appendix-F `H#`

The weighted second-Ursell tree term has already been reduced to the
root-marked vertex-product sum in `AppendixFSecondUrsellMarkedFugacity`.  This
module packages that reduction in the source-facing CMP116 interfaces: a
future leaf-summation/source theorem may bound the marked vertex sum, and Lean
then supplies the weighted tree, geometric profile, `cluster3`, and UV
consumers.

No analytic leaf summation, first-activity estimate, `hRpoly`, continuum
construction, or Clay conclusion is proved here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped BigOperators

namespace YangMills.RG

variable {d L : ℕ} [NeZero L]

/-! ## Activity-carrier recasting and canonical active roots -/

/-- Recast an active polymer between two activity carriers.  The underlying
set and all hole/skeleton properties are independent of the activity map. -/
noncomputable def omegaPolymerReindex
    (HF : HoleFamily d L)
    {z z' : Finset (Cube d L) → ℂ}
    (P : OmegaPolymerType HF z) :
    OmegaPolymerType HF z' :=
  ⟨P.val, P.property⟩

@[simp] theorem omegaPolymerReindex_val
    (HF : HoleFamily d L)
    {z z' : Finset (Cube d L) → ℂ}
    (P : OmegaPolymerType HF z) :
    (omegaPolymerReindex HF (z' := z') P).val = P.val :=
  rfl

/-- A canonical, choice-based active skeleton root for an omega polymer. -/
noncomputable def omegaPolymerSkeletonRoot
    (HF : HoleFamily d L)
    {z : Finset (Cube d L) → ℂ}
    (P : OmegaPolymerType HF z) :
    Cube d L :=
  Classical.choose P.property.right.right.right

/-- The canonical active root really lies in the active skeleton. -/
theorem omegaPolymerSkeletonRoot_mem
    (HF : HoleFamily d L)
    {z : Finset (Cube d L) → ℂ}
    (P : OmegaPolymerType HF z) :
    omegaPolymerSkeletonRoot HF P ∈ skeleton HF P.val :=
  Classical.choose_spec P.property.right.right.right

/-! ## From marked vertex sums to weighted tree sums -/

/-- Canonical-root version of
`appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootVertexSum`.
The future source theorem only has to bound the marked vertex sum at the
canonical active root of the target polymer. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_canonicalMarkedRootVertexSum
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Q : OmegaPolymerType HF zK)
    (n : ℕ)
    (Croot Cleaf decay : ℝ)
    (hw : ∀ P : OmegaPolymerType HF zK, 0 ≤ w P)
    (hvertex :
      appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zK w
          (omegaPolymerSkeletonRoot HF Q) n ≤
        Croot * decay * Cleaf ^ n) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Q.val n ≤
      Croot * decay * ((4 : ℝ) * Cleaf) ^ n :=
  appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootVertexSum
    HF zK w Q (omegaPolymerSkeletonRoot HF Q) n
    Croot Cleaf decay hw (omegaPolymerSkeletonRoot_mem HF Q) hvertex

/-! ## CMP116 constructors from marked vertex-sum source bounds -/

/-- CMP116 geometric `H#` profile from a source theorem bounding the
root-marked vertex-product sum.  The finite tree-shape aggregation pays the
explicit ratio factor `4`, so the profile smallness hypothesis uses
`((4 * Cleaf) * epsilon) < 1`. -/
noncomputable def
    balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_markedRootVertex_geometric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (w : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon Croot Cleaf : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hCroot0 : ∀ t k, 0 ≤ Croot t k)
    (hCleaf0 : ∀ t k, 0 ≤ Cleaf t k)
    (hρ1 : ∀ t k, ((4 : ℝ) * Cleaf t k) * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hvertex :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k)
            (w t k)
            (omegaPolymerSkeletonRoot HF
              (omegaPolymerReindex HF
                (z' := balabanCMP116AppendixFIntegratedKsharpActivityFamily
                  HF z Λ F ν t k) P)) n ≤
          Croot t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf t k ^ n)
    (hBclosed :
      ∀ t k,
        (Croot t k * epsilon t k) *
            (1 - ((4 : ℝ) * Cleaf t k) * epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    BalabanCMP116AppendixFHsharpGeometricMajorantProfile
      HF zCarrier z Λ F ν g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric
    HF zCarrier z Λ F ν g w epsilon Croot
    (fun t k => (4 : ℝ) * Cleaf t k)
    hε hCroot0
    (fun t k => mul_nonneg (by norm_num) (hCleaf0 t k))
    hρ1 hw hactivity
    (fun t k P n => by
      let zInt :=
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k
      let Q : OmegaPolymerType HF zInt :=
        omegaPolymerReindex HF (z' := zInt) P
      have hv :
          appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF zInt
              (w t k) (omegaPolymerSkeletonRoot HF Q) n ≤
            Croot t k *
              Real.exp
                (-(polymerClusterResidualRate κ κ₀ *
                  ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
              Cleaf t k ^ n := by
        simpa [Q, zInt] using hvertex t k P n
      have htree :=
        appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_canonicalMarkedRootVertexSum
          HF zInt (w t k) Q n (Croot t k) (Cleaf t k)
          (Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
          (hw t k) hv
      simpa [Q, zInt] using htree)
    hBclosed

/-- Source-normal `cluster3` constructor from the marked root vertex-sum
estimate plus pointwise first-activity extraction. -/
noncomputable def
    balabanCMP116AppendixFHsharpCluster3Contract_of_markedRootVertex_geometric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (g : ℕ → ℝ)
    (w : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon Croot Cleaf : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hinput : Prop) (hinput_holds : hinput)
    (hultralocal : Prop) (hultralocal_holds : hultralocal)
    (hlocal : Prop) (hlocal_holds : hlocal)
    (hinfluence : Prop) (hinfluence_holds : hinfluence)
    (hmargin : 3 * κ₀ + 3 ≤ κ)
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hCroot0 : ∀ t k, 0 ≤ Croot t k)
    (hCleaf0 : ∀ t k, 0 ≤ Cleaf t k)
    (hρ1 : ∀ t k, ((4 : ℝ) * Cleaf t k) * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hvertex :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k)
            (w t k)
            (omegaPolymerSkeletonRoot HF
              (omegaPolymerReindex HF
                (z' := balabanCMP116AppendixFIntegratedKsharpActivityFamily
                  HF z Λ F ν t k) P)) n ≤
          Croot t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf t k ^ n)
    (hBclosed :
      ∀ t k,
        (Croot t k * epsilon t k) *
            (1 - ((4 : ℝ) * Cleaf t k) * epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpCluster3Contract HF zCarrier
      (fun t k Y =>
        balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  balabanCMP116AppendixFHsharpCluster3Contract_of_profile
    HF zCarrier z Λ F ν g
    hinput hinput_holds hultralocal hultralocal_holds
    hlocal hlocal_holds hinfluence hinfluence_holds hmargin
    (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_markedRootVertex_geometric
      HF zCarrier z Λ F ν g w epsilon Croot Cleaf
      hε hCroot0 hCleaf0 hρ1 hw hactivity hvertex hBclosed)

/-- Real-part omega-rooted UV decay fed directly by the marked root
vertex-sum estimate plus pointwise first-activity extraction. -/
theorem
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_markedRootVertex_geometric
    {d L : ℕ} [NeZero L] {lieDim : Nat}
    {β : Type*} [MeasurableSpace β]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (w : ∀ t k,
      OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k) → ℝ)
    (epsilon Croot Cleaf : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val))
    (hε : ∀ t k, 0 ≤ epsilon t k)
    (hCroot0 : ∀ t k, 0 ≤ Croot t k)
    (hCleaf0 : ∀ t k, 0 ≤ Cleaf t k)
    (hρ1 : ∀ t k, ((4 : ℝ) * Cleaf t k) * epsilon t k < 1)
    (hw :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)), 0 ≤ w t k Q)
    (hactivity :
      ∀ t k (Q : OmegaPolymerType HF
        (balabanCMP116AppendixFIntegratedKsharpActivityFamily
          HF z Λ F ν t k)),
        ‖balabanCMP116AppendixFIntegratedKsharpActivityFamily
            HF z Λ F ν t k Q.val‖ ≤ epsilon t k * w t k Q)
    (hvertex :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpWeightedTreeMarkedRootVertexSum HF
            (balabanCMP116AppendixFIntegratedKsharpActivityFamily
              HF z Λ F ν t k)
            (w t k)
            (omegaPolymerSkeletonRoot HF
              (omegaPolymerReindex HF
                (z' := balabanCMP116AppendixFIntegratedKsharpActivityFamily
                  HF z Λ F ν t k) P)) n ≤
          Croot t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf t k ^ n)
    (hBclosed :
      ∀ t k,
        (Croot t k * epsilon t k) *
            (1 - ((4 : ℝ) * Cleaf t k) * epsilon t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ :=
  singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_profile
    HF zCarrier r z Λ F ν Rsc g
    hC hH₀ hg hκ hR
    (balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_markedRootVertex_geometric
      HF zCarrier z Λ F ν g w epsilon Croot Cleaf
      hε hCroot0 hCleaf0 hρ1 hw hactivity hvertex hBclosed)
    hdisj hnoedges hholes_ne hCq

end YangMills.RG
