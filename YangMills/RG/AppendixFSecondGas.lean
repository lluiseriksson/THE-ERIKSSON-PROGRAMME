/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFKsharp
import YangMills.RG.LocalKP
import YangMills.KP.MayerInversion

/-!
# Appendix F: the second hard-core gas from evaluated `K#`

This module exposes the second Appendix-F gas after the first connected
activity has been integrated:

```
K#(Y, psi)  ->  z_K(Y) := K#(Y, psi)
```

and instantiates that scalar activity through the already-existing
`omegaHolePolymerSystem`.  It also records the later scalar normalization
obtained after integrating the spectator field:

```
z_K(Y) := ∫ K#(Y, psi) dnu(psi).
```

The module is intentionally structural.  It does not prove Dimock's closed
estimate for `K#`, does not assert convergence of the later Ursell series, and
does not hide the KP-ready smallness and geometry assumptions.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

variable {d L : ℕ} [NeZero L]
variable {β : Type*} [MeasurableSpace β]
variable {Ψ : Cube d L → Type*}

/-- The evaluated first integrated activity, regarded as the scalar activity
of the second Appendix-F gas. -/
noncomputable def appendixFHoleSecondGasActivity
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L)) : ℂ :=
  (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ

/-- The second hard-core gas produced by the evaluated `K#` activity.  Its
carrier is the source-facing with-holes `omegaHolePolymerSystem`; target sets
that are not representable by a first connected cover have zero activity. -/
noncomputable def appendixFHoleSecondGas
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (ψ : ∀ x, Ψ x) :
    KP.PolymerSystem :=
  omegaHolePolymerSystem HF
    (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ)

noncomputable instance appendixFHoleSecondGas_fintype
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (ψ : ∀ x, Ψ x) :
    Fintype (appendixFHoleSecondGas HF z Λ Hraw μ ψ).Polymer :=
  inferInstanceAs (Fintype
    (omegaHolePolymerSystem HF
      (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ)).Polymer)

@[simp] theorem appendixFHoleSecondGas_activity
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (ψ : ∀ x, Ψ x)
    (Y : (appendixFHoleSecondGas HF z Λ Hraw μ ψ).Polymer) :
    (appendixFHoleSecondGas HF z Λ Hraw μ ψ).activity Y =
      (appendixFHoleKsharp HF z Λ Hraw μ Y.val).globalEval ψ := by
  rfl

/-- The evaluated `K#` activity is zero away from the target region generated
by first connected source-facing covers. -/
theorem appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L))
    (hY : Y ∉ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ) :
    appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ Y = 0 := by
  classical
  let fiber :=
    appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y
  have hfiber : fiber = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro C hC
    have hCdata :
        C ∈ appendixFConnectedCoverRegion
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          Λ ∧
        appendixFCoverUnion
          (fun X : OmegaPolymerType HF z => X.val) C = Y := by
      simpa [fiber] using
        (mem_appendixFTargetFiber_iff
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          (fun X : OmegaPolymerType HF z => X.val)
          Λ Y C).mp hC
    apply hY
    rw [appendixFTargetRegion]
    exact Finset.mem_image.mpr ⟨C, hCdata.1, hCdata.2⟩
  unfold appendixFHoleSecondGasActivity
  rw [appendixFHoleKsharp_globalEval]
  have hzero :
      (fun φ : (∀ _ : Cube d L, β) =>
        (appendixFHoleConnectedLocalActivity HF z Λ Hraw Y).globalEval ψ φ)
        =
      fun _ => 0 := by
    funext φ
    rw [appendixFHoleConnectedLocalActivity_globalEval]
    simp [appendixFHoleConnectedMayerActivity, appendixFConnectedMayerActivity,
      fiber, hfiber]
  rw [hzero]
  simp

/-- A KP-ready pointwise majorant for the evaluated second gas.  This is
deliberately stronger than the source-shaped Dimock `(642)` estimate: it
contains exactly the tilt and cardinality factors consumed by the current KP
criterion. -/
def AppendixFHoleSecondGasKPMajorant
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (ψ : ∀ x, Ψ x)
    (t q A : ℝ) : Prop :=
  ∀ Y : (appendixFHoleSecondGas HF z Λ Hraw μ ψ).Polymer,
    Real.exp t *
        ‖(appendixFHoleSecondGas HF z Λ Hraw μ ψ).activity Y‖ *
        Real.exp (Y.val.card : ℝ)
      ≤ A * q ^ (discreteModifiedMetric HF Y.val + 1)

/-- The evaluated second gas satisfies the standard `omegaHolePolymerSystem` KP
criterion whenever its activity is given by an explicit KP-ready majorant. -/
theorem appendixFHoleSecondGas_KPCriterion_of_majorant
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β)
    (ψ : ∀ x, Ψ x)
    (t q A : ℝ)
    (hA0 : 0 ≤ A)
    (hK :
      AppendixFHoleSecondGasKPMajorant
        HF z Λ Hraw μ ψ t q A)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)) < 1)
    (hsmall :
      A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (q * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    KP.KPCriterion
      ((appendixFHoleSecondGas HF z Λ Hraw μ ψ).scaleActivity
        (Real.exp t))
      (fun Y => (Y.val.card : ℝ)) := by
  change
    KP.KPCriterion
      ((omegaHolePolymerSystem HF
          (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ)).scaleActivity
        (Real.exp t))
      (fun Y => (Y.val.card : ℝ))
  refine
    omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound
      HF (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ)
      t q A hA0 ?_ hdisj hnoedges hholes_ne hq0 hCq hsmall
  intro Y
  simpa [AppendixFHoleSecondGasKPMajorant, appendixFHoleSecondGas] using hK Y

/-! ## Spectator-integrated scalar `K#` activity -/

variable {γ : Type*} [MeasurableSpace γ]

/-- The spectator-integrated scalar first activity.  This is the source-shaped
`z_K(Y)` family that can be fed into the second `omegaHolePolymerSystem` and
then into the `H#`/source-majorant layer.

No quantitative estimate is implied by this definition: it is just the
spectator integral of the already-defined `K#` local functional. -/
noncomputable def appendixFHoleIntegratedKsharpActivity
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β)
    (Y : Finset (Cube d L)) : ℂ :=
  ∫ ψ : (∀ _ : Cube d L, β),
    (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ
    ∂(Measure.pi fun _ : Cube d L => ν)

@[simp] theorem appendixFHoleIntegratedKsharpActivity_eq_integral
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β)
    (Y : Finset (Cube d L)) :
    appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν Y =
      ∫ ψ : (∀ _ : Cube d L, β),
        (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ
        ∂(Measure.pi fun _ : Cube d L => ν) := rfl

/-- A spectator-integrated `K#` scalar inherits any uniform bound on the
spectator-field evaluation of `K#`.

This is only a probability-integral transfer.  It does not supply the
pointwise `K#` estimate or the spectator measure; both remain source inputs. -/
theorem norm_appendixFHoleIntegratedKsharpActivity_le_of_globalEval_bound
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β) [IsProbabilityMeasure ν]
    (Y : Finset (Cube d L)) {B : ℝ}
    (hK : ∀ ψ : (∀ _ : Cube d L, β),
      ‖(appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ‖ ≤ B) :
    ‖appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν Y‖ ≤ B := by
  have hbound := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun _ : Cube d L => ν)
    (f := fun ψ : (∀ _ : Cube d L, β) =>
      (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ)
    (C := B)
    (MeasureTheory.ae_of_all _ hK)
  simpa [appendixFHoleIntegratedKsharpActivity, measure_univ] using hbound

/-- The spectator-integrated `K#` activity still vanishes away from the
target region generated by first connected source-facing covers. -/
theorem appendixFHoleIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β)
    (Y : Finset (Cube d L))
    (hY : Y ∉ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ) :
    appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν Y = 0 := by
  unfold appendixFHoleIntegratedKsharpActivity
  have hzero :
      (fun ψ : (∀ _ : Cube d L, β) =>
        (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ)
        =
      fun _ => 0 := by
    funext ψ
    exact appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion
      HF z Λ Hraw μ ψ Y hY
  rw [hzero]
  simp

/-- The second hard-core gas formed from the spectator-integrated scalar
`K#` activity.  This is the actual scalar carrier expected by the later
`H#` source-majorant interface. -/
noncomputable def appendixFHoleIntegratedSecondGas
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β) :
    KP.PolymerSystem :=
  omegaHolePolymerSystem HF
    (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν)

noncomputable instance appendixFHoleIntegratedSecondGas_fintype
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β) :
    Fintype (appendixFHoleIntegratedSecondGas HF z Λ Hraw μ ν).Polymer :=
  inferInstanceAs (Fintype
    (omegaHolePolymerSystem HF
      (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν)).Polymer)

@[simp] theorem appendixFHoleIntegratedSecondGas_activity
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β)
    (Y : (appendixFHoleIntegratedSecondGas HF z Λ Hraw μ ν).Polymer) :
    (appendixFHoleIntegratedSecondGas HF z Λ Hraw μ ν).activity Y =
      appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν Y.val := by
  rfl

/-- Finite target-family integration rewritten in the scalar `z_K` language.
The left side is the spectator integral of the finite `K#` target-family gas;
the right side is the same finite hard-core target-family sum using the
spectator-integrated scalar activity.

This is the normalization contract between the finite `K#` factorization layer
and the later `omegaHolePolymerSystem`/`H#` source-majorant layer. -/
theorem integral_sum_appendixFHoleKsharp_eq_sum_prod_integratedKsharpActivity_of_admissibleTargetFamilies
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : Measure γ)
    (ν : Measure β) [IsProbabilityMeasure ν] [Nonempty β]
    (hHsub : ∀ X, X ∈ Λ → (Hraw X).spectatorSupport ⊆ skeleton HF X.val)
    (hint : ∀ targets,
      targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ →
        Integrable
          (fun ψ : (∀ _ : Cube d L, β) =>
            ∏ Y ∈ targets,
              (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ)
          (Measure.pi fun _ : Cube d L => ν)) :
    ∫ ψ : (∀ _ : Cube d L, β),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ)
        ∂(Measure.pi fun _ : Cube d L => ν)
      =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν Y := by
  calc
    (∫ ψ : (∀ _ : Cube d L, β),
        (∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
          ∏ Y ∈ targets,
            (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ)
        ∂(Measure.pi fun _ : Cube d L => ν))
        =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          ∫ ψ : (∀ _ : Cube d L, β),
            (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ
            ∂(Measure.pi fun _ : Cube d L => ν) := by
        exact
          integral_sum_appendixFHoleKsharp_eq_sum_prod_integral_of_admissibleTargetFamilies
            HF z Λ Hraw μ ν hHsub hint
    _ =
      ∑ targets ∈ appendixFHoleAdmissibleTargetFamilies HF z Λ,
        ∏ Y ∈ targets,
          appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν Y := by
        refine Finset.sum_congr rfl ?_
        intro targets _htargets
        refine Finset.prod_congr rfl ?_
        intro Y _hY
        rfl

end YangMills.RG
