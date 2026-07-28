/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import MarkedRootedClosure.PaperTheorems
import MarkedRootedClosure.NonVacuity

/-!
Run with:

```bash
lake build MarkedRootedClosure          # first
lake env lean MarkedRootedClosure/Oracle.lean
```

The output should list only the standard classical axioms inherited from
Mathlib and the pinned upstream proof development:
`[propext, Classical.choice, Quot.sound]` for every theorem below.
-/

#print axioms MarkedRootedClosure.normalizedRootedChildFactorialTreeBound
#print axioms MarkedRootedClosure.normalizedRootedChildFactorialTreeCatalanIdentity
#print axioms MarkedRootedClosure.markedRootCatalanBound
#print axioms MarkedRootedClosure.markedRootLeafGeometricBound
#print axioms MarkedRootedClosure.targetPreservingWeightedTreeBound
#print axioms MarkedRootedClosure.NonVacuity.nonvacuous_markedRootLeafGeometricBound
#print axioms MarkedRootedClosure.NonVacuity.nonvacuous_targetPreservingWeightedTreeBound
