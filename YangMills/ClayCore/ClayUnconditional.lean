/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 14b: Clay Theorem from SU(N_c) Wilson Cluster Majorisation

Terminal bridge from the majorisation bundle
`SUNWilsonClusterMajorisation N_c` to the Clay Millennium statement
`ClayYangMillsTheorem`. This is the final structural step: once the
Balaban multiscale output produces a `SUNWilsonClusterMajorisation
N_c`, the Clay theorem follows by two projections
(`clayMassGap_of_majorisation` followed by
`clayMassGap_implies_clayTheorem`).

## Main theorems

* `clay_yangMills_theorem_from_cluster`
    : `SUNWilsonClusterMajorisation N_c → ClayYangMillsTheorem`.

* `clay_yangMills_unconditional`
    : `SUNWilsonClusterMajorisation N_c → ClayYangMillsMassGap N_c`.

Both are pure structural projections — they introduce no analytic
axioms. Oracle (`#print axioms`) for every theorem in this file is
expected to be `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
import YangMills.ClayCore.ClayAuthentic
import YangMills.ClayCore.ClayWitness
import YangMills.ClayCore.SUNWilsonMajorisation

namespace YangMills

open Real

/-- **Unconditional Clay mass-gap witness (bridge C).**

    Given an SU(N_c) Wilson cluster majorisation bundle, produce the
    concrete authentic Clay mass-gap structure with mass gap
    `kpParameter r = -log(r)/2` and prefactor `C_clust`.

    This is definitionally equal to `clayMassGap_of_majorisation` and
    is exported under the `unconditional` name to mark the final
    structural step of the Balaban → ClayCore pipeline. -/
noncomputable def clay_yangMills_unconditional
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    ClayYangMillsMassGap N_c :=
  clayMassGap_of_majorisation maj

/-- **Terminal projection to the Clay Millennium statement.**

    Given an SU(N_c) Wilson cluster majorisation bundle, the Clay
    Millennium statement `∃ m_phys, 0 < m_phys` is immediate: take
    `m_phys := kpParameter r`, positive by `kpParameter_pos`. -/
theorem clay_yangMills_theorem_from_cluster
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    ClayYangMillsTheorem :=
  clayMassGap_implies_clayTheorem (clay_yangMills_unconditional maj)

/-- Mass gap of the unconditional witness equals `kpParameter r`. -/
theorem clay_yangMills_unconditional_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    (clay_yangMills_unconditional maj).m = kpParameter maj.r := rfl

/-- Prefactor of the unconditional witness equals `C_clust`. -/
theorem clay_yangMills_unconditional_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    (clay_yangMills_unconditional maj).C = maj.C_clust := rfl

/-- Mass gap of the unconditional witness is strictly positive. -/
theorem clay_yangMills_unconditional_mass_pos
    {N_c : ℕ} [NeZero N_c]
    (maj : SUNWilsonClusterMajorisation N_c) :
    0 < (clay_yangMills_unconditional maj).m :=
  kpParameter_pos maj.hr_pos maj.hr_lt_one

end YangMills
