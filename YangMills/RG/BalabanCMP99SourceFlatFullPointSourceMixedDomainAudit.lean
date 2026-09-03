/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceMixedDomain

/-!
# PRE-VALIDATION audit: mixed centered/physical full Eq. (2.46) domains

Source is present; its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.  The audit checks the four
proof-bearing declarations; the two mixed momentum objects are definitions
and do not enlarge the audit denominator.
-/

#print axioms YangMills.RG.cmp99SourceFlatQprime_centered_eq_physical_or_add_period
#print axioms YangMills.RG.cmp89Eq249CentralEntireAveragePair_mixedCoarse_ne_zero
#print axioms YangMills.RG.cmp99SourceFlatFullPointSourceSolutionDomain_mixed
#print axioms YangMills.RG.cmp89Eq246PhysicalFineToFineGreenIntegrand_centered_eq_physical
