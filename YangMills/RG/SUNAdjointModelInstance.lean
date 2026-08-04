/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.SUNAdjointDimension
import YangMills.RG.PhysicalGaugeCochains

/-!
# The TRUE adjoint model — P4-ADJ brick 3 (the last brick)
(`hRpoly` campaign — plan §3ter P4-ADJ; bricks 1, 2a, 2b = Addenda 486,
488, 490)

This module CLOSES the P4-ADJ obligation registered in Addendum 477: the
concrete matricial adjoint model of `SU(n)`, as an honest instance of
`SUNAdjointModel n`:

* **`Module.Finite ℝ (SuLie n)`** — finiteness by the NOETHERIAN route:
  the ambient matrix space is module-finite over `ℝ`, hence Noetherian;
  `su(n)` injects into it via `Submodule.subtype`, so it is Noetherian,
  and its `⊤` submodule is finitely generated.  This route avoids BOTH
  broken chains at this pin: the direct submodule-finiteness instance
  synthesis (probe-isolated, Addendum 490) and a trace-removing
  projection `skew → su(n)` (killed by cross-instance `SMul ℝ ℂ`
  mismatches in entry-level goals — measured, v7).
* **`suLieCoordIso`** — the isometric coordinate transport
  `SuLie n ≃ₗᵢ[ℝ] SUNLieCoord n`, from `stdOrthonormalBasis` reindexed
  along `finrank_suLie : finrank ℝ (SuLie n) = n² − 1` (brick 2b).
* **`matrixSUNAdjointModel n : SUNAdjointModel n`** — THE TRUE MODEL:
  `adCLM g` is the conjugation of the packaged adjoint action
  `suAdActLin g` (brick 2a) by the coordinate isometry, made continuous
  by finite-dimensionality.  `ad_one`/`ad_mul` come from the brick-2a
  action laws; `ad_inner` comes from `inner_suAdActLin` transported
  through `LinearIsometryEquiv.inner_map_map`.  The action provenance is
  DEFINITIONAL: `adCLM g` is literally `g · X · gᴴ` read through fixed
  orthonormal coordinates — nothing is hypothesis-carried.

**Honest scope.**  This discharges the P4-ADJ registration: the trivial
witness of Addendum 477 is no longer the only instance, and the
flat-lane theorems can now be instantiated at the TRUE model.  The
coordinate system is the (noncanonical) `stdOrthonormalBasis` choice —
any other orthonormal choice conjugates the model by a fixed orthogonal
map; nothing downstream depends on the choice.  This does NOT identify
the flat shell with the interacting Wilson Hessian, and does not touch
volume-uniform Poincaré, root localization, G5, `hRpoly`, mass gap, or
Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

variable {n : ℕ}

/-! ## Finiteness of `su(n)` (the Noetherian route) -/

/-- `su(n)` is finite-dimensional: the subtype injects into the
finite (hence Noetherian over `ℝ`) ambient matrix space. -/
instance (n : ℕ) : Module.Finite ℝ (SuLie n) := by
  have h1 : IsNoetherian ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    isNoetherian_of_isNoetherianRing_of_finite ℝ (Matrix (Fin n) (Fin n) ℂ)
  have h2 : IsNoetherian ℝ ↥(suMatrixSubmodule n) :=
    isNoetherian_of_injective (suMatrixSubmodule n).subtype
      (Submodule.injective_subtype _)
  have h3 : IsNoetherian ℝ (SuLie n) := h2
  exact ⟨IsNoetherian.noetherian ⊤⟩
/-! ## The isometric coordinate transport -/

/-- The isometric identification of `su(n)` with the abstract coordinate
space `SUNLieCoord n = EuclideanSpace ℝ (Fin (n²−1))`, via the standard
orthonormal basis reindexed along the brick-2b dimension count. -/
noncomputable def suLieCoordIso (n : ℕ) [NeZero n] :
    SuLie n ≃ₗᵢ[ℝ] SUNLieCoord n :=
  ((stdOrthonormalBasis ℝ (SuLie n)).reindex
    (finCongr (finrank_suLie n))).repr

/-! ## The true adjoint model -/

/-- **THE TRUE ADJOINT MODEL** (P4-ADJ closed): `Ad(g) X = g·X·gᴴ` on
`su(n)`, read through the fixed orthonormal coordinates of
`suLieCoordIso`, as an instance of `SUNAdjointModel n`. -/
noncomputable def matrixSUNAdjointModel (n : ℕ) [NeZero n] :
    SUNAdjointModel n where
  adCLM g := LinearMap.toContinuousLinearMap
    ((((suLieCoordIso n).toLinearEquiv.toLinearMap).comp
        (suAdActLin g)).comp
      ((suLieCoordIso n).symm.toLinearEquiv.toLinearMap))
  ad_one := by
    apply ContinuousLinearMap.ext
    intro x
    show (suLieCoordIso n) (suAdActLin 1 ((suLieCoordIso n).symm x)) = x
    rw [suAdActLin_one]
    show (suLieCoordIso n) ((suLieCoordIso n).symm x) = x
    exact (suLieCoordIso n).apply_symm_apply x
  ad_mul g h := by
    apply ContinuousLinearMap.ext
    intro x
    show (suLieCoordIso n) (suAdActLin (g * h) ((suLieCoordIso n).symm x))
      = (suLieCoordIso n) (suAdActLin g ((suLieCoordIso n).symm
          ((suLieCoordIso n) (suAdActLin h ((suLieCoordIso n).symm x)))))
    rw [suAdActLin_mul, (suLieCoordIso n).symm_apply_apply]
    rfl
  ad_inner g X Y := by
    show inner ℝ
        ((suLieCoordIso n) (suAdActLin g ((suLieCoordIso n).symm X)))
        ((suLieCoordIso n) (suAdActLin g ((suLieCoordIso n).symm Y)))
      = inner ℝ X Y
    rw [(suLieCoordIso n).inner_map_map, inner_suAdActLin]
    exact (suLieCoordIso n).symm.inner_map_map X Y

end YangMills.RG
