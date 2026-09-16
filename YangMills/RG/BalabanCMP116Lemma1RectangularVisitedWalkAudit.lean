/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma1RectangularVisitedWalk

/-!
# Axiom audit for rectangular visited walks

Compiler validation: source checkpoint `0ee9133a1b0c3d0eeaebcd3d9964e3ae06476ca9`
was materialized in one fresh Colab Pro+ CPU/high-RAM clone on 2026-08-03;
this audit exited zero and all five declarations used only
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms YangMills.RG.CMP99GeneralizedWalk.rectangularTerm
#print axioms YangMills.RG.cmp116Lemma1RectangularGeneratedWalkMonomial_eq_visited
#print axioms YangMills.RG.CMP116Lemma1RectangularWalkSourceCertificate.propagator
#print axioms YangMills.RG.CMP116Lemma1RectangularWalkSourceCertificate.propagator_one
#print axioms YangMills.RG.CMP116Lemma1RectangularWalkSourceCertificate.norm_propagator_apply_le
