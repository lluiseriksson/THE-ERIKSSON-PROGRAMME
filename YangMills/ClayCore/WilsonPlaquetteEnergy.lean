/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# Phase 9a: Wilson Plaquette Energy

Concrete plaquette energy for the SU(N_c) Wilson lattice action:
  `wilsonPlaquetteEnergy N_c U := Re (tr U)`.

This is the canonical choice in lattice Yang–Mills.  Pinning the
plaquette energy to this real-analytic class function rules out the
vacuous witness `plaquetteEnergy := 0` that would collapse the Gibbs
measure to the product Haar reference.

## Main results

* `wilsonPlaquetteEnergy_continuous`   — continuity on SU(N_c).
* `wilsonPlaquetteEnergy_one`          — value at identity equals `N_c`.
* `wilsonPlaquetteEnergy_nontrivial`   — not identically zero when `N_c > 0`.
* `wilsonPlaquetteEnergy_bounded`      — `|E(U)| ≤ N_c` for all U in SU(N_c).
-/

namespace YangMills

open Matrix Complex

noncomputable section

/-- Wilson plaquette energy for SU(N_c): real part of the trace of `U`.

    This is the canonical single-plaquette action used in lattice gauge
    theory, up to the overall sign and normalisation convention. -/
noncomputable def wilsonPlaquetteEnergy (N_c : ℕ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) : ℝ :=
  (Matrix.trace U.val).re

/-- Continuity of the Wilson plaquette energy as a function on SU(N_c). -/
theorem wilsonPlaquetteEnergy_continuous (N_c : ℕ) :
    Continuous (wilsonPlaquetteEnergy N_c) := by
  unfold wilsonPlaquetteEnergy
  refine Complex.continuous_re.comp ?_
  refine Continuous.comp ?_ continuous_subtype_val
  -- `Matrix.trace M = ∑ i, M i i`; continuity follows from
  -- continuity of projections in a product topology.
  change Continuous (fun M : Matrix (Fin N_c) (Fin N_c) ℂ => Matrix.trace M)
  refine continuous_finset_sum _ (fun i _ => ?_)
  exact (continuous_apply (α := fun _ : Fin N_c => ℂ) i).comp
        (continuous_apply (α := fun _ : Fin N_c => (Fin N_c → ℂ)) i)

/-- The Wilson plaquette energy at the identity element of SU(N_c) equals `N_c`. -/
theorem wilsonPlaquetteEnergy_one (N_c : ℕ) :
    wilsonPlaquetteEnergy N_c
        (1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      = (N_c : ℝ) := by
  unfold wilsonPlaquetteEnergy
  have h1 :
      ((1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) : Matrix (Fin N_c) (Fin N_c) ℂ)
        = (1 : Matrix (Fin N_c) (Fin N_c) ℂ) :=
    OneMemClass.coe_one _
  rw [h1, Matrix.trace_one]
  simp

/-- The Wilson plaquette energy is not identically zero when `N_c > 0`:
    it evaluates to `N_c > 0` at the identity, ruling out the trivial
    plaquette energy `fun _ => 0` as an alias of `wilsonPlaquetteEnergy`. -/
theorem wilsonPlaquetteEnergy_nontrivial {N_c : ℕ} (hN : 0 < N_c) :
    wilsonPlaquetteEnergy N_c
        (1 : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      ≠ 0 := by
  rw [wilsonPlaquetteEnergy_one]
  exact_mod_cast hN.ne'

/-- Weaker boundedness form consumed by the Clay–authentic structure:
    there exists a uniform bound on `|wilsonPlaquetteEnergy N_c U|`
    for all `U ∈ SU(N_c)`. -/
theorem wilsonPlaquetteEnergy_bounded (N_c : ℕ) :
    ∃ M : ℝ, ∀ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      |wilsonPlaquetteEnergy N_c U| ≤ M := by
  by_cases hN : NeZero N_c
  · haveI := hN
    refine ⟨sSup (Set.range (fun U =>
              |wilsonPlaquetteEnergy N_c U|)) + 1, ?_⟩
    intro U
    have hrange_bdd :
        BddAbove (Set.range (fun U =>
            |wilsonPlaquetteEnergy N_c U|)) := by
      have hcont :
          Continuous (fun U => |wilsonPlaquetteEnergy N_c U|) :=
        (wilsonPlaquetteEnergy_continuous N_c).abs
      exact (isCompact_range hcont).bddAbove
    have hle : |wilsonPlaquetteEnergy N_c U|
                  ≤ sSup (Set.range (fun U =>
                      |wilsonPlaquetteEnergy N_c U|)) :=
      le_csSup hrange_bdd ⟨U, rfl⟩
    linarith
  · refine ⟨0, ?_⟩
    intro U
    have : N_c = 0 := by
      by_contra hne
      exact hN ⟨hne⟩
    subst this
    simp [wilsonPlaquetteEnergy, Matrix.trace, Fintype.sum_empty]

end

end YangMills
