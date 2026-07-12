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
import AmosClosure.BesselRealDeriv
import AmosClosure.RiccatiReal
import AmosClosure.AmosBoundProofReal
import AmosClosure.AmosBarrierReal
import AmosClosure.AmosFamily
import AmosClosure.AmosLowerReal

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

/- Mid-course external audit of C4 phase 1 (2026-07-12, adjustment
2): the two charter non-vacuity anchors converted from `example` to
named theorems and registered.  44 total at this registration. -/
#print axioms AmosClosure.besselIReal_zero_eq
#print axioms AmosClosure.besselIReal_one_eq

/- C4 phase 2 (charter Amendment 2, J-C4-2): the derivative layer at
real order, per the registered lemma sequence + the rpow split
helper, the deriv/log forms, and the nu = n consistency value test.
Nine entries; 53 total at this registration. -/
#print axioms AmosClosure.rpow_add_two_mul
#print axioms AmosClosure.besselRealTerm_hasDerivAt
#print axioms AmosClosure.besselRealTerm_deriv_zero_bound
#print axioms AmosClosure.besselRealTerm_deriv_succ_bound
#print axioms AmosClosure.summable_besselRealDerivMajorant
#print axioms AmosClosure.besselIReal_hasDerivAt
#print axioms AmosClosure.besselIReal_deriv_identity
#print axioms AmosClosure.besselIReal_log_hasDerivAt
#print axioms AmosClosure.besselIReal_deriv_value_natCast

/- C4 phase 3a (charter Amendment 3, J-C4-3 first block): the Riccati
structure at real order.  Eight entries; 61 total at this
registration. -/
#print axioms AmosClosure.besselRatioReal_pos
#print axioms AmosClosure.besselRatioReal_hasDerivAt
#print axioms AmosClosure.amosRHS_pos_of_nonneg
#print axioms AmosClosure.amosRHS_calibration_real
#print axioms AmosClosure.riccatiQReal_amosRHS
#print axioms AmosClosure.riccatiQReal_pos_of_lt
#print axioms AmosClosure.besselPsiReal_hasDerivAt
#print axioms AmosClosure.riccati_zero_of_real_touch

/- C4 phase 3b (charter Amendment 4, J-C4-3 second block): the zone
at real order, uniformity isolated in the two named lemmas.  Seven
entries; 68 total at this registration. -/
#print axioms AmosClosure.besselRealTerm_le_geometric
#print axioms AmosClosure.besselIReal_mul_le
#print axioms AmosClosure.besselRealTerm_zero_lt_besselIReal
#print axioms AmosClosure.besselRealTerm_zero_succ
#print axioms AmosClosure.real_zone_ratio_uniform
#print axioms AmosClosure.real_zone_coefficient_bound
#print axioms AmosClosure.besselPsiReal_zone

/- C4 phase 3c (charter Amendment 5, J-C4-3 closing block): the
barrier, THE THEOREM at real order, both consumers, and the two
registered locks.  Six entries; 74 total at this registration. -/
#print axioms AmosClosure.besselPsiReal_gt
#print axioms AmosClosure.amosBoundReal_holds
#print axioms AmosClosure.besselIReal_unit_step
#print axioms AmosClosure.besselIReal_logDeriv_lt
#print axioms AmosClosure.amosBound_holds_recovered
#print axioms AmosClosure.amosBoundReal_half_order

/- C5 phase 1 (charter docs/C5-CHARTER.md + Amendments 1-2,
J-C5-1): the one-parameter family, the general-c nullcline
trichotomy, and the sufficiency half of the classification.  Nine
entries; 83 total at this registration. -/
#print axioms AmosClosure.amosFamily_pos
#print axioms AmosClosure.amosFamily_half
#print axioms AmosClosure.amosFamily_calibration
#print axioms AmosClosure.riccatiQReal_amosFamily
#print axioms AmosClosure.riccatiQReal_amosFamily_pos
#print axioms AmosClosure.riccatiQReal_amosFamily_neg
#print axioms AmosClosure.riccatiQReal_amosFamily_zero
#print axioms AmosClosure.amosFamily_anti
#print axioms AmosClosure.amosFamily_upper_of_le_half

/- C5 phase 2 (charter Amendments 1-2, J-C5-2): the ratio
recurrence, the lower bound BY RECURRENCE FROM C4, the explicit
witness, and THE UNIFORM CLASSIFICATION.  Five entries; 88 total
at this registration. -/
#print axioms AmosClosure.besselIReal_ratio_recurrence
#print axioms AmosClosure.amosLower_pos
#print axioms AmosClosure.besselLowerReal_holds
#print axioms AmosClosure.amosFamily_lt_amosLower_witness
#print axioms AmosClosure.amosFamily_uniform_upper_iff
