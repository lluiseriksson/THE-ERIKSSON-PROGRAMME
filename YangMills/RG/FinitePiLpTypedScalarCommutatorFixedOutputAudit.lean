/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedScalarCommutatorFixedOutput

/-!
# Axiom audit for fixed-output scalar-commutator bounds

Compiler-verified at exact source checkpoint
`4e23216a121fc64451528ce050443ee460ce589a` in cold GitHub Actions run
`30992627475`; both declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms YangMills.RG.finitePiLpTypedFixedOutputWeightedKernelBound_scalarCommutator
#print axioms YangMills.RG.finitePiLpTypedExponentialKernelBound_of_fixedOutputWeighted
