import YangMills.RG.LocalFunctional
import YangMills.L1_GibbsMeasure.EdgeFactorization

/-!
# Ultralocal product-measure factorization

This file records the product-measure factorization substrate consumed by the
type-local polymer layer.  It is deliberately finite-dimensional: the measure
is an explicit product `Measure.pi`, and locality is supplied by
`LocalFunctional` / `LocalActivity` support declarations.

The result is not a cluster expansion and does not prove the Dimock activity
decay.  It isolates the elementary independence step that such a construction
uses after activities have been localized.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

namespace LocalFunctional

/-- Two local functionals with disjoint supports factorize under an ultralocal
product probability measure. -/
theorem integral_mul_of_disjoint_support
    {Site β : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (F G : LocalFunctional Site (fun _ => β) ℂ)
    (hdisj : Disjoint F.support G.support) :
    ∫ φ, F.globalEval φ * G.globalEval φ ∂(Measure.pi fun _ : Site => μ)
      = (∫ φ, F.globalEval φ ∂(Measure.pi fun _ : Site => μ)) *
        ∫ φ, G.globalEval φ ∂(Measure.pi fun _ : Site => μ) := by
  classical
  refine YangMills.integral_mul_of_disjoint_deps_complex μ
    (fun i : Site => i ∈ F.support) (fun φ => F.globalEval φ)
    (fun φ => G.globalEval φ) ?_ ?_
  · intro x y hxy
    exact F.globalEval_eq_of_agreeOn (fun i hi => hxy i hi)
  · intro x y hxy
    exact G.globalEval_eq_of_agreeOn (fun i hiG =>
      hxy i (fun hiF => Finset.disjoint_left.mp hdisj hiF hiG))

end LocalFunctional

namespace LocalActivity

/-- For fixed spectator field, two activities with disjoint fluctuation
supports factorize under an ultralocal product probability measure on the
fluctuation field. -/
theorem integral_mul_of_disjoint_fluctuationSupport
    {Site β : Type*} [Fintype Site] [DecidableEq Site]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (F G : LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hdisj : Disjoint F.fluctuationSupport G.fluctuationSupport) :
    ∫ φ, F.globalEval ψ φ * G.globalEval ψ φ ∂(Measure.pi fun _ : Site => μ)
      = (∫ φ, F.globalEval ψ φ ∂(Measure.pi fun _ : Site => μ)) *
        ∫ φ, G.globalEval ψ φ ∂(Measure.pi fun _ : Site => μ) := by
  classical
  refine YangMills.integral_mul_of_disjoint_deps_complex μ
    (fun i : Site => i ∈ F.fluctuationSupport) (fun φ => F.globalEval ψ φ)
    (fun φ => G.globalEval ψ φ) ?_ ?_
  · intro x y hxy
    exact F.globalEval_eq_of_agreeOn (fun i _hi => rfl) (fun i hi => hxy i hi)
  · intro x y hxy
    exact G.globalEval_eq_of_agreeOn (fun i _hi => rfl) (fun i hiG =>
      hxy i (fun hiF => Finset.disjoint_left.mp hdisj hiF hiG))

end LocalActivity

end YangMills.RG
