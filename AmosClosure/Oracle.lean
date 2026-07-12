/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.Core
import AmosClosure.NonVacuity
import AmosClosure.BesselInterface
import AmosClosure.BesselDeriv
import AmosClosure.Riccati
import AmosClosure.AmosBoundProof
import AmosClosure.AmosBarrier
import AmosClosure.BesselRealInterface

/-!
Run with:

```bash
lake build AmosClosure          # first
lake env lean AmosClosure/Oracle.lean
```

Every theorem below must print exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms AmosClosure.amos_calibration
#print axioms AmosClosure.amos_small
#print axioms AmosClosure.phi_unit_step
#print axioms AmosClosure.phi_step_of_recurrences
#print axioms AmosClosure.unit_step_of_recurrence_and_amos
#print axioms AmosClosure.logderiv_unit_step_increase
#print axioms AmosClosure.NonVacuity.nonvacuous_phi_step
#print axioms AmosClosure.NonVacuity.nonvacuous_unit_step
#print axioms AmosClosure.summable_besselTerm
#print axioms AmosClosure.besselI_pos
#print axioms AmosClosure.besselI_recurrence
#print axioms AmosClosure.besselI_ratio_recurrence
#print axioms AmosClosure.besselI_unit_step
#print axioms AmosClosure.besselI_logderiv_step
#print axioms AmosClosure.besselI_phi_step
#print axioms AmosClosure.besselI_hasDerivAt
#print axioms AmosClosure.besselI_log_hasDerivAt
#print axioms AmosClosure.besselI_logDeriv_lt
#print axioms AmosClosure.besselRatio_hasDerivAt
#print axioms AmosClosure.amosRHS_calibration
#print axioms AmosClosure.riccatiQ_amosRHS
#print axioms AmosClosure.riccatiQ_pos_of_lt
#print axioms AmosClosure.besselPsi_zone
#print axioms AmosClosure.besselPsi_gt
#print axioms AmosClosure.amosBound_holds
#print axioms AmosClosure.besselI_unit_step_unconditional
#print axioms AmosClosure.besselI_logDeriv_lt_unconditional
#print axioms AmosClosure.besselI_phi_step_unconditional

/- v2 extension (C3 audit round 1, hostile-editor finding #2): the six
supporting lemmas named in the C3 paper's artifact map, registered so
every "exact" row carries a DIRECT oracle witness, not a transitive
one.  34 entries at the c3-v1.0 release. -/
#print axioms AmosClosure.besselTerm_le_geometric
#print axioms AmosClosure.besselI_mul_le
#print axioms AmosClosure.besselTerm_zero_lt_besselI
#print axioms AmosClosure.besselTerm_zero_succ
#print axioms AmosClosure.besselPsi_hasDerivAt
#print axioms AmosClosure.riccati_zero_of_touch

/- C4 phase 1 (charter docs/C4-CHARTER.md, J-C4-1): the real-order
Gamma-series interface and THE IDENTIFICATION THEOREM.  Eight
entries; 42 total at this registration. -/
#print axioms AmosClosure.summable_besselRealTerm
#print axioms AmosClosure.besselIReal_pos
#print axioms AmosClosure.gamma_le_gamma_add
#print axioms AmosClosure.besselRealTerm_succ
#print axioms AmosClosure.besselRealTerm_rec_zero
#print axioms AmosClosure.besselRealTerm_rec_succ
#print axioms AmosClosure.besselIReal_recurrence
#print axioms AmosClosure.besselIReal_natCast
