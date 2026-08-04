/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinVolumeRestriction

/-!
# D-7 — transport of finite Ising volumes across a site equivalence

This is the chart-change lemma used after an active subvolume has been cut out
of a common ambient chart.  It is an exact reindexing of two finite sums.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Pull a coupling matrix back along a site equivalence. -/
noncomputable def reindexCoupling (e : κ ≃ ι) (J : ι → ι → ℝ) :
    κ → κ → ℝ :=
  fun a b => J (e a) (e b)

/-- The induced equivalence of spin configurations. -/
noncomputable def configEquiv (e : κ ≃ ι) :
    (κ → Fin 2) ≃ (ι → Fin 2) :=
  Equiv.arrowCongr e (Equiv.refl (Fin 2))

theorem configEquiv_apply (e : κ ≃ ι) (η : κ → Fin 2) (i : ι) :
    configEquiv e η i = η (e.symm i) := by
  rfl

/-- Ising weights are invariant under a bijective relabelling of sites. -/
theorem isingWeight_reindexCoupling
    (e : κ ≃ ι) (J : ι → ι → ℝ) (η : κ → Fin 2) :
    isingWeight (reindexCoupling e J) η =
      isingWeight J (configEquiv e η) := by
  have hinner : ∀ a : κ,
      (∑ b : κ, J (e a) (e b) * spin (η a) * spin (η b)) =
        ∑ j : ι, J (e a) j * spin (η a) * spin (η (e.symm j)) := by
    intro a
    simpa using e.sum_comp
      (fun j : ι => J (e a) j * spin (η a) * spin (η (e.symm j)))
  have henergy :
      (∑ a : κ, ∑ b : κ, J (e a) (e b) * spin (η a) * spin (η b)) =
        ∑ i : ι, ∑ j : ι,
          J i j * spin (η (e.symm i)) * spin (η (e.symm j)) := by
    rw [Finset.sum_congr rfl fun a _ => hinner a]
    simpa using e.sum_comp
      (fun i : ι => ∑ j : ι,
        J i j * spin (η (e.symm i)) * spin (η (e.symm j)))
  unfold isingWeight reindexCoupling
  rw [henergy]
  rfl

/-- Gibbs expectations are invariant under a bijective relabelling of sites. -/
theorem expect_gibbs_reindex
    (e : κ ≃ ι) (J : ι → ι → ℝ)
    (f : (ι → Fin 2) → ℝ) :
    expect (gibbsMu (isingWeight (reindexCoupling e J)))
        (fun η => f (configEquiv e η)) =
      expect (gibbsMu (isingWeight J)) f := by
  let wκ : (κ → Fin 2) → ℝ := isingWeight (reindexCoupling e J)
  let wι : (ι → Fin 2) → ℝ := isingWeight J
  have hweight : ∀ η : κ → Fin 2, wκ η = wι (configEquiv e η) := by
    intro η
    exact isingWeight_reindexCoupling e J η
  have hZ : gibbsZ wκ = gibbsZ wι := by
    unfold gibbsZ
    calc
      ∑ η, wκ η = ∑ η, wι (configEquiv e η) :=
        Finset.sum_congr rfl fun η _ => hweight η
      _ = ∑ ξ, wι ξ := (configEquiv e).sum_comp wι
  unfold expect gibbsMu
  rw [hZ]
  calc
    ∑ η, wκ η / gibbsZ wι * f (configEquiv e η)
        = ∑ η, wι (configEquiv e η) / gibbsZ wι * f (configEquiv e η) :=
      Finset.sum_congr rfl fun η _ => by rw [hweight η]
    _ = ∑ ξ, wι ξ / gibbsZ wι * f ξ :=
      (configEquiv e).sum_comp (fun ξ => wι ξ / gibbsZ wι * f ξ)

end Dobrushin

end YangMills.OS
