import Mathlib.Topology.Continuous

/-!
Mathlib-only elaboration gate for the explicitly pinned `ContinuousAt.comp'`
used by the A--E contour telescope.  This runs before the project graph.
-/

example {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (x : X)
    (hg : ContinuousAt g (f x)) (hf : ContinuousAt f x) :
    ContinuousAt (fun y => g (f y)) x :=
  ContinuousAt.comp' (f := f) (g := g) hg hf
