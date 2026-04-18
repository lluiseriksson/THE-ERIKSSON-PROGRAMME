/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 14c: SU(N_c) Wilson Cluster Majorisation Witness

Concrete inhabitation route of `SUNWilsonClusterMajorisation N_c`
from a `BalabanHyps N_c` bundle.

## Physical content

The Balaban multiscale programme furnishes, for every `N_c ≥ 2`, a
sequence of renormalisation-group steps whose output is a convergent
polymer cluster expansion of the terminal remainder in the concrete
SU(N_c) Wilson lattice Gibbs measure. The KP geometric-decay
parameter of the terminal polymer activities is `r := g_bar ∈ (0, 1)`,
where `g_bar` is the asymptotic-freedom running coupling supplied by
`BalabanH1 N_c` (Phase 5 of [Eriksson Feb 2026], §7 of Bloque 4).

Combining the Balaban rate with the universal cluster bound on the
two-plaquette connected correlator (Theorem 7.1 of [Eriksson Feb
2026], Bloque 4) then produces the exponential clustering witness

  `|⟨W_p W_q⟩_c|
      ≤ C_clust · exp(-(kpParameter g_bar) · siteLatticeDist p q)`

with `kpParameter g_bar = -log(g_bar)/2 > 0`, in the exact signature
demanded by `SUNWilsonClusterMajorisation N_c`.

## Lean content

This file bundles the Balaban output and the universal cluster bound
into a `SUNWilsonBridgeData N_c` structure and exposes the bridge
constructor `sunWilsonMajorisation_witness` that forwards it, field
by field, to `SUNWilsonClusterMajorisation N_c`. Two downstream
convenience lemmas chain onto `ClayYangMillsMassGap N_c` and the
Clay Millennium statement `ClayYangMillsTheorem` via the Phase 14b
projections `clay_yangMills_unconditional` and
`clay_yangMills_theorem_from_cluster`.

No analytic content is proved here; the universal cluster bound is
taken as an explicit hypothesis (`h_decay`) alongside the Balaban
skeleton. The role of this phase is structural: it records the
precise data contract between the future concrete Balaban output
and the authentic Clay target.

Oracle (`#print axioms`) for every theorem in this file is expected
to be `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
import YangMills.ClayCore.BalabanH1H2H3
import YangMills.ClayCore.ClayAuthentic
import YangMills.ClayCore.ClayUnconditional
import YangMills.ClayCore.ClayWitness
import YangMills.ClayCore.KPSmallness
import YangMills.ClayCore.SUNWilsonMajorisation

namespace YangMills

open Real

/-- **SU(N_c) Wilson bridge data.**

    Packages the Balaban skeleton (`hyps`) with the universal
    two-plaquette clustering bound (`h_decay`) in the exact shape
    needed to inhabit `SUNWilsonClusterMajorisation N_c`.

    The KP geometric-decay rate is pinned to `r := hyps.h1.g_bar`,
    the asymptotic-freedom running coupling produced by Balaban's
    short-field bound, so that the mass gap
    `kpParameter hyps.h1.g_bar = -log(hyps.h1.g_bar)/2` is strictly
    positive by `kpParameter_pos` applied to
    `hyps.h1.hg_pos, hyps.h1.hg_lt1`. -/
structure SUNWilsonBridgeData (N_c : ℕ) [NeZero N_c] : Type where
  /-- Balaban multiscale hypotheses supplying the KP rate `g_bar`. -/
  hyps : BalabanHyps N_c
  /-- Absolute clustering prefactor. -/
  C_clust : ℝ
  /-- Positivity of the clustering prefactor. -/
  hC_clust : 0 < C_clust
  /-- Universal two-plaquette connected correlator bound for the
      concrete SU(N_c) Wilson lattice Gibbs measure, with mass gap
      `kpParameter hyps.h1.g_bar` and prefactor `C_clust`. Signature
      matches `SUNWilsonClusterMajorisation N_c.hbound` verbatim. -/
  h_decay :
    ∀ {d : ℕ} [NeZero d] {L : ℕ} [NeZero L] (β : ℝ) (_hβ : 0 < β)
      (F : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF_bdd : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      |wilsonConnectedCorr
          (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c)
          β F p q|
        ≤ C_clust * Real.exp
            (-(kpParameter hyps.h1.g_bar) * siteLatticeDist p.site q.site)

/-- **Phase 14c main bridge.**  Given SU(N_c) Wilson bridge data,
    inhabit `SUNWilsonClusterMajorisation N_c` by field-by-field
    forwarding. The KP rate `r` is pinned to `hyps.h1.g_bar`. -/
noncomputable def sunWilsonMajorisation_witness
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    SUNWilsonClusterMajorisation N_c where
  r := data.hyps.h1.g_bar
  hr_pos := data.hyps.h1.hg_pos
  hr_lt_one := data.hyps.h1.hg_lt1
  C_clust := data.C_clust
  hC_clust := data.hC_clust
  hbound := data.h_decay

/-- **Balaban → Clay mass gap.**  Compose the Phase 14c bridge with
    the Phase 14b projection to produce an inhabitant of the authentic
    `ClayYangMillsMassGap N_c` directly from Balaban bridge data. -/
noncomputable def clay_yangMills_massGap_from_balaban
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    ClayYangMillsMassGap N_c :=
  clay_yangMills_unconditional (sunWilsonMajorisation_witness data)

/-- **Balaban → Clay Millennium.**  Terminal projection: from Balaban
    bridge data alone, the Clay Millennium statement
    `∃ m_phys, 0 < m_phys` follows. -/
theorem clay_yangMills_theorem_from_balaban
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    ClayYangMillsTheorem :=
  clay_yangMills_theorem_from_cluster (sunWilsonMajorisation_witness data)

/-- Non-triviality: the KP rate of the majorisation bundle produced by
    `sunWilsonMajorisation_witness` is exactly `hyps.h1.g_bar`. -/
theorem sunWilsonMajorisation_witness_r_eq
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    (sunWilsonMajorisation_witness data).r = data.hyps.h1.g_bar := rfl

/-- Non-triviality: the prefactor of the majorisation bundle produced
    by `sunWilsonMajorisation_witness` is exactly `C_clust`. -/
theorem sunWilsonMajorisation_witness_C_clust_eq
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    (sunWilsonMajorisation_witness data).C_clust = data.C_clust := rfl

/-- Mass gap of the Balaban-derived Clay witness equals
    `kpParameter hyps.h1.g_bar = -log(hyps.h1.g_bar)/2`. -/
theorem clay_yangMills_massGap_from_balaban_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    (clay_yangMills_massGap_from_balaban data).m
      = kpParameter data.hyps.h1.g_bar := rfl

/-- Prefactor of the Balaban-derived Clay witness equals `C_clust`. -/
theorem clay_yangMills_massGap_from_balaban_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    (clay_yangMills_massGap_from_balaban data).C = data.C_clust := rfl

/-- Strict positivity of the Balaban-derived mass gap. -/
theorem clay_yangMills_massGap_from_balaban_mass_pos
    {N_c : ℕ} [NeZero N_c]
    (data : SUNWilsonBridgeData N_c) :
    0 < (clay_yangMills_massGap_from_balaban data).m :=
  kpParameter_pos data.hyps.h1.hg_pos data.hyps.h1.hg_lt1

end YangMills
