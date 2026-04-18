/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 14a: SU(N_c) Wilson Cluster Majorisation

Generic (N_c ≥ 2) abstraction of the Wilson two-plaquette exponential
cluster bound, in the exact signature required by `ClayWitnessHyp
N_c.hbound_hyp`.

## Physical content

For the concrete SU(N_c) Wilson lattice Gibbs measure at inverse
coupling `β > 0`, the connected two-plaquette correlator
`|⟨W_p W_q⟩_c|` decays exponentially in the Euclidean site distance
between `p.site` and `q.site`. The decay is controlled by the KP
parameter `m := kpParameter r = -log(r)/2` with `r ∈ (0, 1)`, and the
prefactor `C_clust > 0` is absolute (independent of `d`, `L`, `β`,
and the observable `F`).

## Lean content

This file packages that bound into a hypothesis structure
`SUNWilsonClusterMajorisation N_c`, whose fields are identical in
shape to those of `ClayWitnessHyp N_c`, and exposes three forwarding
lemmas:

* `clayWitnessHyp_of_majorisation`   — projection to `ClayWitnessHyp`.
* `clayMassGap_of_majorisation`      — end-to-end Clay witness.
* `massGap_pos_of_majorisation`      — non-triviality (the gap is
  strictly positive).

No analytic content is proved here; the Wilson cluster bound is taken
as an explicit hypothesis and forwarded field-by-field. The role of
this phase is structural: it interpolates between the future Balaban
multiscale outputs (supplying `hbound` via a concrete derivation) and
the authentic Clay target.

Oracle (`#print axioms`) for every theorem in this file is expected to
be `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
import YangMills.ClayCore.ClayAuthentic
import YangMills.ClayCore.ClayWitness
import YangMills.ClayCore.KPSmallness

namespace YangMills

open Real

/-- **SU(N_c) Wilson cluster majorisation (hypothesis bundle).**

    Packages the universal two-plaquette connected correlator bound
    for the concrete SU(N_c) Wilson lattice Gibbs measure, in the
    exact signature required by `ClayWitnessHyp N_c.hbound_hyp`.

    Field dictionary:
    * `r`, `hr_pos`, `hr_lt_one` — KP geometric decay rate.
    * `C_clust`, `hC_clust`      — absolute clustering prefactor.
    * `hbound`                   — universal exponential bound on
      `|wilsonConnectedCorr _ _ β F p q|` by
      `C_clust · exp(-(kpParameter r) · siteLatticeDist p.site q.site)`. -/
structure SUNWilsonClusterMajorisation (N_c : ℕ) [NeZero N_c] : Type where
  /-- The KP geometric-decay parameter `r ∈ (0, 1)`. -/
  r : ℝ
  /-- Positivity of `r`. -/
  hr_pos : 0 < r
  /-- Upper bound `r < 1`. -/
  hr_lt_one : r < 1
  /-- Absolute clustering prefactor. -/
  C_clust : ℝ
  /-- Positivity of the clustering prefactor. -/
  hC_clust : 0 < C_clust
  /-- The universal two-plaquette connected correlator bound,
      with `m := kpParameter r` and `C := C_clust`. Signature is
      identical to `ClayWitnessHyp N_c.hbound_hyp`. -/
  hbound :
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

/-- **Bridge A.** Forward an SU(N_c) Wilson cluster majorisation bundle
    to the generic Clay witness hypothesis bundle. Field-by-field
    projection; no analytic content. -/
noncomputable def clayWitnessHyp_of_majorisation
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    ClayWitnessHyp N_c where
  r := maj.r
  hr_pos := maj.hr_pos
  hr_lt_one := maj.hr_lt_one
  C_clust := maj.C_clust
  hC_clust := maj.hC_clust
  hbound_hyp := maj.hbound

/-- **Bridge B.** Given an SU(N_c) Wilson cluster majorisation bundle,
    produce a concrete inhabitant of `ClayYangMillsMassGap N_c` with
    mass gap `kpParameter r` and prefactor `C_clust`. -/
noncomputable def clayMassGap_of_majorisation
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    ClayYangMillsMassGap N_c :=
  clay_yangMills_witness (clayWitnessHyp_of_majorisation maj)

/-- Non-triviality: the mass gap extracted from a majorisation bundle
    equals `kpParameter r = -log(r)/2`. -/
theorem clayMassGap_of_majorisation_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    (clayMassGap_of_majorisation maj).m = kpParameter maj.r := rfl

/-- Non-triviality: the prefactor extracted from a majorisation bundle
    equals `C_clust`. -/
theorem clayMassGap_of_majorisation_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    (clayMassGap_of_majorisation maj).C = maj.C_clust := rfl

/-- **Mass gap positivity.** The mass gap produced by the majorisation
    bundle is strictly positive. Proof: `kpParameter_pos` applied to
    `0 < r < 1`. -/
theorem massGap_pos_of_majorisation
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    0 < (clayMassGap_of_majorisation maj).m :=
  kpParameter_pos maj.hr_pos maj.hr_lt_one

end YangMills
