/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.L6_OS.OsterwalderSchrader
import YangMills.L6_OS.AbelianU1ClusterProperty
import YangMills.L6_OS.AbelianU1Reflection

/-!
# SU(1) discharge of `OSCovariant` and `HasInfiniteVolumeLimit`

This module completes the **OS-axiom quartet** at SU(1):

| OS axiom               | SU(1) discharge file              | Phase |
|------------------------|-----------------------------------|-------|
| OS1 (Covariance)       | THIS FILE                         | 50    |
| OS2 (Reflection pos.)  | `AbelianU1Reflection.lean`        | 46+47 |
| OS4 (Cluster property) | `AbelianU1ClusterProperty.lean`   | 49    |
| Inf-vol limit          | THIS FILE                         | 50    |

Together with Phases 46–49, this file closes every OS-style structural
axiom referenced in `OsterwalderSchrader.lean` for the trivial-group
SU(1) case, fully unconditionally.

## Bundle theorems

* `osTriple_su1` — bundles `(OSCovariant, OSClusterProperty,
  HasInfiniteVolumeLimit)` over an arbitrary observable type.
* `osQuadruple_su1` — bundles all FOUR (incl. `OSReflectionPositive`)
  by specialising the observable type to `X → ℝ` so all four axioms
  share a uniform interface.

## Why the proofs are short

The pattern is the same as Phases 46–49: SU(1)'s
`GaugeConfig d L SU(1)` is a `Subsingleton`, so:

* **Every endomorphism `f : X → X` equals `id`** (by `funext` +
  `Subsingleton.elim`). Hence `Measure.map (act s) μ = Measure.map id μ
  = μ`.
* **Every real-valued function `f : X → ℝ` is constant**, equal to
  `f default`. Hence under any probability measure
  `∫ x, f x ∂μ = f default`. So sequences of integrals are constant,
  and all such sequences converge to the same limit.

## Caveat

The trivial-group physics-degeneracy caveat (`COWORK_FINDINGS.md`
Finding 003) applies. For `N_c ≥ 2`, OS covariance is the
Euclidean-group invariance of the lattice action plus the
infinite-volume measure (substantive), and the infinite-volume limit
existence is a measure-tightness obligation (substantive).

## Oracle target

`[propext, Classical.choice, Quot.sound]` per project discipline.

-/

namespace YangMills.L6_OS

open MeasureTheory

variable {d L : ℕ} [NeZero d] [NeZero L]

/-! ## §1. OSCovariant — unconditional for SU(1) -/

/-- **`OSCovariant` discharged unconditionally for SU(1)**, with arbitrary
    symmetry type `Symm` and arbitrary action
    `act : Symm → X → X`. The action is forced to be the identity
    because `X = GaugeConfig d L SU(1)` is `Subsingleton`. -/
theorem osCovariant_su1
    (β : ℝ) (Symm : Type*)
    (act : Symm → GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) →
                  GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) :
    OSCovariant
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      Symm act := by
  intro s _hmeas
  have h_id : act s = id := by
    funext U
    exact Subsingleton.elim _ _
  rw [h_id]
  exact MeasureTheory.Measure.map_id

#print axioms osCovariant_su1

/-! ## §2. HasInfiniteVolumeLimit — unconditional for SU(1) -/

/-- **`HasInfiniteVolumeLimit` discharged unconditionally for SU(1)**,
    with arbitrary sequence of probability measures `muN N` and
    arbitrary probability limit `muInf` on the SU(1) gauge-config
    space. Every integrand is constant (Subsingleton), so integrals
    are constant in `N`, and a constant sequence converges to its
    value (which equals the limiting integral by the same constancy
    argument). -/
theorem hasInfiniteVolumeLimit_su1
    (muN : ℕ → Measure (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)))
    (muInf : Measure (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)))
    (h_muN_prob : ∀ N, IsProbabilityMeasure (muN N))
    [IsProbabilityMeasure muInf]
    (Obs : Type*)
    (evalObs : Obs → GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ) :
    HasInfiniteVolumeLimit muN muInf Obs evalObs := by
  intro O
  -- Both LHS and RHS reduce to `evalObs O default`.
  have hN : ∀ N, (∫ U, evalObs O U ∂(muN N)) = evalObs O default := fun N => by
    haveI : IsProbabilityMeasure (muN N) := h_muN_prob N
    have h :
        (fun U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) =>
          evalObs O U) = (fun _ => evalObs O default) := by
      funext U; rw [Subsingleton.elim U default]
    rw [h]; simp
  have hInf : (∫ U, evalObs O U ∂muInf) = evalObs O default := by
    have h :
        (fun U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) =>
          evalObs O U) = (fun _ => evalObs O default) := by
      funext U; rw [Subsingleton.elim U default]
    rw [h]; simp
  rw [hInf]
  simp_rw [hN]
  exact tendsto_const_nhds

#print axioms hasInfiniteVolumeLimit_su1

/-! ## §3. The full OS-axiom quartet bundle for SU(1) -/

/-- **Bundle: the SU(1) Wilson Gibbs measure satisfies all four
    OS-style structural axioms simultaneously**, fully unconditionally.

    The four conjuncts:
    1. `OSCovariant` for any symmetry / action (Phase 50, `osCovariant_su1`).
    2. `OSReflectionPositive` for `wilsonReflection` (Phase 47,
       `osReflectionPositive_su1` — imported via `AbelianU1Reflection`).
       _Not consumed here directly because the predicate has a different
       observable-type shape; see the `AbelianU1Reflection` companion
       theorem._
    3. `OSClusterProperty` for any observable / dist (Phase 49,
       `osClusterProperty_su1`).
    4. `HasInfiniteVolumeLimit` against any sequence of probability
       measures (Phase 50, `hasInfiniteVolumeLimit_su1`).

    The bundling theorem here returns the `(OSCovariant, OSCluster,
    HasInfVolLim)` triple for a **single** unified observable type and
    action setup.

    For the four-axiom **conjunction** including `OSReflectionPositive`,
    see `osQuadruple_su1` defined later in this section. -/
theorem osTriple_su1
    (β : ℝ) (Symm : Type*)
    (act : Symm → GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) →
                  GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ))
    (Obs : Type*)
    (evalObs : Obs → GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (distObs : Obs → Obs → ℝ)
    (muN : ℕ → Measure (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)))
    (h_muN_prob : ∀ N, IsProbabilityMeasure (muN N)) :
    OSCovariant
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      Symm act ∧
    OSClusterProperty
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      Obs evalObs distObs ∧
    HasInfiniteVolumeLimit muN
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      Obs evalObs := by
  refine ⟨?_, ?_, ?_⟩
  · exact osCovariant_su1 β Symm act
  · exact osClusterProperty_su1 β Obs evalObs distObs
  · exact hasInfiniteVolumeLimit_su1 muN
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      h_muN_prob Obs evalObs

#print axioms osTriple_su1

/-! ## §3.5. The OS-axiom quartet (with OS-RP) for SU(1) -/

/-- **Full OS-axiom QUARTET bundle for SU(1)**, including
    `OSReflectionPositive`. To make all four axioms share a uniform
    observable interface, we specialise each one to:

    * `Obs := GaugeConfig d L SU(1) → ℝ`  — observables are
      real-valued functions on the gauge-config space.
    * `evalObs F U := F U`                 — evaluation is application.

    With this convention, all four OS-style predicates are stated
    over the same `(Obs, evalObs)` pair and can be conjoined.

    Conjuncts:
    1. `OSCovariant` for any symmetry / action.
    2. `OSReflectionPositive` for `wilsonReflection t` (Phase 47).
    3. `OSClusterProperty` for any `distObs : (X → ℝ) → (X → ℝ) → ℝ`.
    4. `HasInfiniteVolumeLimit` against any sequence of probability
       measures.

    All four discharged unconditionally for SU(1) via the
    Subsingleton-collapse mechanism. -/
theorem osQuadruple_su1
    (β : ℝ) (t : Fin L) (Symm : Type*)
    (act : Symm → GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) →
                  GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ))
    (distObs : (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ) →
               (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ) → ℝ)
    (muN : ℕ → Measure (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)))
    (h_muN_prob : ∀ N, IsProbabilityMeasure (muN N)) :
    OSCovariant
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      Symm act ∧
    OSReflectionPositive
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (fun (F : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
           (U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) => F U)
      (wilsonReflection (G := ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) t) ∧
    OSClusterProperty
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (fun (F : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
           (U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) => F U)
      distObs ∧
    HasInfiniteVolumeLimit muN
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (fun (F : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
           (U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) => F U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact osCovariant_su1 β Symm act
  · exact osReflectionPositive_su1 β t
  · exact osClusterProperty_su1 β
      (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (fun F U => F U) distObs
  · exact hasInfiniteVolumeLimit_su1 muN
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      h_muN_prob
      (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (fun F U => F U)

#print axioms osQuadruple_su1

/-! ## §4. Coordination note -/

/-
The SU(1) OS-axiom landscape after Phase 50:

```
                       SU(1) unconditional?    Witness file
-------------------------------------------------------------------
OSCovariant            ✓ (Phase 50)            AbelianU1OSAxioms (here)
OSReflectionPositive   ✓ (Phase 47)            AbelianU1Reflection
OSClusterProperty      ✓ (Phase 49)            AbelianU1ClusterProperty
HasInfiniteVolumeLimit ✓ (Phase 50)            AbelianU1OSAxioms (here)
wilsonGibbs_RP         ✓ (Phase 46)            AbelianU1Reflection
```

This means: every structural OS-style axiom in `OsterwalderSchrader.lean`
admits a concrete unconditional inhabitant when specialised to the
SU(1) Wilson Gibbs measure. The `osTriple_su1` bundle composes three
of them into a single hypothesis-free theorem.

The trivial-group physics-degeneracy caveat (Finding 003) carries
forward: these are honest **structural** witnesses showing the
predicates are not provably empty, but they are not **physical**
SU(N) Yang-Mills witnesses for `N_c ≥ 2`.

For `N_c ≥ 2`:
* OS covariance: hypercubic-symmetry invariance of `wilsonAction`
  + Haar-invariance + tightness ⇒ infinite-volume invariance.
* OS-RP: Osterwalder-Seiler 1978 / Glimm-Jaffe.
* OS-Cluster: L4 large-field cluster expansion at small β; or
  Bałaban-Magnen-Rivasseau analytic ladder at all β.
* Inf-vol limit: tightness + Prokhorov compactness + measure
  uniqueness on observables.

Cross-references:
- `OsterwalderSchrader.lean` — definitions of `OSCovariant`,
  `OSReflectionPositive`, `OSClusterProperty`,
  `HasInfiniteVolumeLimit`.
- `AbelianU1Unconditional.lean` — SU(1) Subsingleton +
  `gibbs_su1_isProbability`.
- `AbelianU1Reflection.lean` — Phase 46+47 RP companion.
- `AbelianU1ClusterProperty.lean` — Phase 49 OS clustering companion.
- `COWORK_FINDINGS.md` Finding 003 — SU(1) physics-degeneracy caveat.
-/

end YangMills.L6_OS
