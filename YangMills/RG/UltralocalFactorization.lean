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

/-- A finite product of local functionals with pairwise-disjoint supports
factorizes under the ultralocal product probability measure. -/
theorem integral_finsetProd_of_pairwise_disjoint_support
    {Site β ι : Type*} [Fintype Site] [DecidableEq Site] [DecidableEq ι]
    [MeasurableSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (I : Finset ι)
    (F : ι → LocalFunctional Site (fun _ => β) ℂ)
    (hpair : ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j →
      Disjoint (F i).support (F j).support) :
    ∫ φ, (finsetProd I F).globalEval φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      ∏ i ∈ I,
        ∫ φ, (F i).globalEval φ
          ∂(Measure.pi fun _ : Site => μ) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      have heval : ∀ φ : (∀ _ : Site, β),
          (finsetProd (∅ : Finset ι) F).globalEval φ = 1 := by
        intro φ
        simp
      have hleft :
          (∫ φ : (∀ _ : Site, β),
              (finsetProd (∅ : Finset ι) F).globalEval φ
              ∂(Measure.pi fun _ : Site => μ))
            =
          ∫ φ : (∀ _ : Site, β), (1 : ℂ)
              ∂(Measure.pi fun _ : Site => μ) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro φ
        rw [heval φ]
      rw [hleft]
      simp
  | insert a I ha ih =>
      have hpairI : ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j →
          Disjoint (F i).support (F j).support := by
        intro i hi j hj hij
        exact hpair i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      have hdisj :
          Disjoint (F a).support (finsetProd I F).support := by
        change Disjoint (F a).support
          (I.biUnion fun i => (F i).support)
        rw [Finset.disjoint_left]
        intro x hxa hxI
        rcases Finset.mem_biUnion.mp hxI with ⟨j, hj, hxj⟩
        have haj : a ≠ j := by
          intro h
          exact ha (by simpa [h] using hj)
        exact (Finset.disjoint_left.mp
          (hpair a (Finset.mem_insert_self a I)
            j (Finset.mem_insert_of_mem hj) haj) hxa) hxj
      have hprod_eval : ∀ φ : (∀ _ : Site, β),
          (finsetProd (insert a I) F).globalEval φ =
            (F a).globalEval φ * (finsetProd I F).globalEval φ := by
        intro φ
        have hinsert :=
          YangMills.RG.LocalFunctional.globalEval_finsetProd
            (I := insert a I) (F := F) φ
        have hrest :=
          YangMills.RG.LocalFunctional.globalEval_finsetProd
            (I := I) (F := F) φ
        calc
          (finsetProd (insert a I) F).globalEval φ
              =
            ∏ i : {i // i ∈ insert a I}, (F i.1).globalEval φ := hinsert
          _ =
            ∏ i ∈ insert a I, (F i).globalEval φ := by
              simpa using
                (Finset.prod_attach (insert a I)
                  (fun i => (F i).globalEval φ))
          _ =
            (F a).globalEval φ *
              ∏ i ∈ I, (F i).globalEval φ := by
              rw [Finset.prod_insert ha]
          _ =
            (F a).globalEval φ *
              ∏ i : {i // i ∈ I}, (F i.1).globalEval φ := by
              congr 1
              exact (Finset.prod_attach I
                (fun i => (F i).globalEval φ)).symm
          _ =
            (F a).globalEval φ * (finsetProd I F).globalEval φ := by
              rw [hrest]
      have hleft :
          (∫ φ, (finsetProd (insert a I) F).globalEval φ
              ∂(Measure.pi fun _ : Site => μ))
            =
          ∫ φ, (F a).globalEval φ * (finsetProd I F).globalEval φ
              ∂(Measure.pi fun _ : Site => μ) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro φ
        rw [hprod_eval φ]
      have hsplit :=
        integral_mul_of_disjoint_support
          μ (F a) (finsetProd I F) hdisj
      calc
        (∫ φ, (finsetProd (insert a I) F).globalEval φ
            ∂(Measure.pi fun _ : Site => μ))
            =
          ∫ φ, (F a).globalEval φ * (finsetProd I F).globalEval φ
            ∂(Measure.pi fun _ : Site => μ) := hleft
        _ =
          (∫ φ, (F a).globalEval φ
            ∂(Measure.pi fun _ : Site => μ)) *
          ∫ φ, (finsetProd I F).globalEval φ
            ∂(Measure.pi fun _ : Site => μ) := hsplit
        _ =
          (∫ φ, (F a).globalEval φ
            ∂(Measure.pi fun _ : Site => μ)) *
          ∏ i ∈ I,
            ∫ φ, (F i).globalEval φ
              ∂(Measure.pi fun _ : Site => μ) := by
            rw [ih hpairI]
        _ =
          ∏ i ∈ insert a I,
            ∫ φ, (F i).globalEval φ
              ∂(Measure.pi fun _ : Site => μ) := by
            rw [Finset.prod_insert ha]

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

/-- A finite product of local activities with pairwise-disjoint fluctuation
supports factorizes under the ultralocal product probability measure.  The
spectator field is fixed; only the fluctuation field is integrated. -/
theorem integral_finsetProd_of_pairwise_disjoint_fluctuationSupport
    {Site β ι : Type*} [Fintype Site] [DecidableEq Site] [DecidableEq ι]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (I : Finset ι)
    (F : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hpair : ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j →
      Disjoint (F i).fluctuationSupport (F j).fluctuationSupport) :
    ∫ φ, (finsetProd I F).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      ∏ i ∈ I,
        ∫ φ, (F i).globalEval ψ φ
          ∂(Measure.pi fun _ : Site => μ) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      have heval : ∀ φ : (∀ _ : Site, β),
          (finsetProd (∅ : Finset ι) F).globalEval ψ φ = 1 := by
        intro φ
        simp
      have hleft :
          (∫ φ : (∀ _ : Site, β),
              (finsetProd (∅ : Finset ι) F).globalEval ψ φ
              ∂(Measure.pi fun _ : Site => μ))
            =
          ∫ φ : (∀ _ : Site, β), (1 : ℂ)
              ∂(Measure.pi fun _ : Site => μ) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro φ
        rw [heval φ]
      rw [hleft]
      simp
  | insert a I ha ih =>
      have hpairI : ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j →
          Disjoint (F i).fluctuationSupport (F j).fluctuationSupport := by
        intro i hi j hj hij
        exact hpair i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      have hdisj :
          Disjoint (F a).fluctuationSupport (finsetProd I F).fluctuationSupport := by
        change Disjoint (F a).fluctuationSupport
          (I.biUnion fun i => (F i).fluctuationSupport)
        rw [Finset.disjoint_left]
        intro x hxa hxI
        rcases Finset.mem_biUnion.mp hxI with ⟨j, hj, hxj⟩
        have haj : a ≠ j := by
          intro h
          exact ha (by simpa [h] using hj)
        exact (Finset.disjoint_left.mp
          (hpair a (Finset.mem_insert_self a I)
            j (Finset.mem_insert_of_mem hj) haj) hxa) hxj
      have hprod_eval : ∀ φ : (∀ _ : Site, β),
          (finsetProd (insert a I) F).globalEval ψ φ =
            (F a).globalEval ψ φ * (finsetProd I F).globalEval ψ φ := by
        intro φ
        have hinsert :=
          YangMills.RG.LocalActivity.globalEval_finsetProd
            (I := insert a I) (F := F) ψ φ
        have hrest :=
          YangMills.RG.LocalActivity.globalEval_finsetProd
            (I := I) (F := F) ψ φ
        calc
          (finsetProd (insert a I) F).globalEval ψ φ
              =
            ∏ i : {i // i ∈ insert a I}, (F i.1).globalEval ψ φ := hinsert
          _ =
            ∏ i ∈ insert a I, (F i).globalEval ψ φ := by
              simpa using
                (Finset.prod_attach (insert a I)
                  (fun i => (F i).globalEval ψ φ))
          _ =
            (F a).globalEval ψ φ *
              ∏ i ∈ I, (F i).globalEval ψ φ := by
              rw [Finset.prod_insert ha]
          _ =
            (F a).globalEval ψ φ *
              ∏ i : {i // i ∈ I}, (F i.1).globalEval ψ φ := by
              congr 1
              exact (Finset.prod_attach I
                (fun i => (F i).globalEval ψ φ)).symm
          _ =
            (F a).globalEval ψ φ * (finsetProd I F).globalEval ψ φ := by
              rw [hrest]
      have hleft :
          (∫ φ, (finsetProd (insert a I) F).globalEval ψ φ
              ∂(Measure.pi fun _ : Site => μ))
            =
          ∫ φ, (F a).globalEval ψ φ * (finsetProd I F).globalEval ψ φ
              ∂(Measure.pi fun _ : Site => μ) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro φ
        rw [hprod_eval φ]
      have hsplit :=
        integral_mul_of_disjoint_fluctuationSupport
          μ (F a) (finsetProd I F) ψ hdisj
      calc
        (∫ φ, (finsetProd (insert a I) F).globalEval ψ φ
            ∂(Measure.pi fun _ : Site => μ))
            =
          ∫ φ, (F a).globalEval ψ φ * (finsetProd I F).globalEval ψ φ
            ∂(Measure.pi fun _ : Site => μ) := hleft
        _ =
          (∫ φ, (F a).globalEval ψ φ
            ∂(Measure.pi fun _ : Site => μ)) *
          ∫ φ, (finsetProd I F).globalEval ψ φ
            ∂(Measure.pi fun _ : Site => μ) := hsplit
        _ =
          (∫ φ, (F a).globalEval ψ φ
            ∂(Measure.pi fun _ : Site => μ)) *
          ∏ i ∈ I,
            ∫ φ, (F i).globalEval ψ φ
              ∂(Measure.pi fun _ : Site => μ) := by
            rw [ih hpairI]
        _ =
          ∏ i ∈ insert a I,
            ∫ φ, (F i).globalEval ψ φ
              ∂(Measure.pi fun _ : Site => μ) := by
            rw [Finset.prod_insert ha]

end LocalActivity

end YangMills.RG
