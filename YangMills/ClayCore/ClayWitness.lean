/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 7: Clay Witness Assembly

Concrete inhabitant of `ClayYangMillsMassGap N_c` from a bundle of
analytic hypotheses. The mass gap is taken as `m := kpParameter r =
-log(r)/2` with `r ∈ (0, 1)` the Kotecký-Preiss decay parameter. The
prefactor is `C := C_clust` from the terminal two-point cluster bound.
-/
import Mathlib
import YangMills.ClayCore.ClayAuthentic
import YangMills.ClayCore.KPSmallness
import YangMills.ClayCore.ExponentialClustering
import YangMills.ClayCore.MultiscaleDecoupling

namespace YangMills

open Real

/-- Bundle of analytic hypotheses needed to produce the Clay witness.
    `hbound_hyp` packages the universal two-plaquette connected
    correlator bound, with the mass gap identified as `kpParameter r`
    and the prefactor identified as `C_clust`. -/
structure ClayWitnessHyp (N_c : ℕ) [NeZero N_c] : Type where
  /-- The KP geometric-decay parameter `r ∈ (0, 1)`. -/
  r : ℝ
  /-- Positivity of `r`. -/
  hr_pos : 0 < r
  /-- Upper bound `r < 1`. -/
  hr_lt_one : r < 1
  /-- Clustering prefactor. -/
  C_clust : ℝ
  /-- Positivity of the clustering prefactor. -/
  hC_clust : 0 < C_clust
  /-- The universal two-plaquette connected correlator bound,
      with `m := kpParameter r` and `C := C_clust`. -/
  hbound_hyp :
    ∀ {d : ℕ} [NeZero d] {L : ℕ} [NeZero L] (β : ℝ) (_hβ : 0 < β)
      (F : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF_bdd : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      |wilsonConnectedCorr
          (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c)
          β F p q|
        ≤ C_clust * Real.exp (-(kpParameter r) * siteLatticeDist p.site q.site)

/-- **Clay witness**: given a bundle of analytic hypotheses, produce a
    concrete inhabitant of the authentic Clay mass-gap structure. -/
noncomputable def clay_yangMills_witness {N_c : ℕ} [NeZero N_c]
    (hyp : ClayWitnessHyp N_c) : ClayYangMillsMassGap N_c where
  m := kpParameter hyp.r
  hm := kpParameter_pos hyp.hr_pos hyp.hr_lt_one
  C := hyp.C_clust
  hC := hyp.hC_clust
  hbound := fun β hβ F hF_bdd p q h_sep =>
    hyp.hbound_hyp β hβ F hF_bdd p q h_sep

/-- Non-triviality: the mass gap produced by the witness is the KP
    parameter `-log(r)/2`. -/
theorem clay_yangMills_witness_mass_eq {N_c : ℕ} [NeZero N_c]
    (hyp : ClayWitnessHyp N_c) :
    (clay_yangMills_witness hyp).m = kpParameter hyp.r := rfl

/-- Non-triviality: the prefactor produced by the witness is `C_clust`. -/
theorem clay_yangMills_witness_prefactor_eq {N_c : ℕ} [NeZero N_c]
    (hyp : ClayWitnessHyp N_c) :
    (clay_yangMills_witness hyp).C = hyp.C_clust := rfl

end YangMills