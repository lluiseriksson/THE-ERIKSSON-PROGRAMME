/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalWindowGeometry

/-!
# The measured geometric bridge for separated plaquettes

There are two different indices in a scaling argument.  At a fixed scale,
the coordinates of the embedded plaquettes are fixed and the thermodynamic
volume tends to infinity.  Only after the infinite-volume correlation bound
has been obtained may the scale tend to infinity.

The repository already proves that coordinates move by at most the length of
a seam-avoiding touching walk.  The lemmas below turn that result into the
lower bound on `touchGraph.dist` needed by the correlation theorem.  They
also expose the remaining obligation: reachability and sufficient margin for
a shortest walk must be constructed for the concrete embedded plaquettes in
each sufficiently large thermodynamic volume.
-/

namespace YangMills.Continuum

open YangMills

variable {d N : ℕ} [NeZero N]

/-- If a shortest touching walk avoids the periodic seam, displacement in
one coordinate is at most its graph distance. -/
theorem site_le_add_touchGraph_dist_of_margin
    {p q : ConcretePlaquette d N}
    (hreach : (touchGraph d N).Reachable p q)
    (hmargin : p.SiteMargin ((touchGraph d N).dist p q))
    (j : Fin d) :
    (q.site j).val ≤
      (p.site j).val + (touchGraph d N).dist p q := by
  obtain ⟨W, hW⟩ := hreach.exists_walk_length_eq_dist
  have hp : p.SiteMargin W.length := by
    simpa [hW] using hmargin
  have hbound :=
    ConcretePlaquette.site_le_add_length_of_touchWalk W hp j
  simpa [hW] using hbound

/-- Coordinate separation yields the required lower graph-distance bound
once the fixed-volume reachability and no-wrap certificates are present. -/
theorem le_touchGraph_dist_of_site_separation
    {p q : ConcretePlaquette d N}
    (hreach : (touchGraph d N).Reachable p q)
    (hmargin : p.SiteMargin ((touchGraph d N).dist p q))
    (j : Fin d) (k : ℕ)
    (hsep : (p.site j).val + k ≤ (q.site j).val) :
    k ≤ (touchGraph d N).dist p q := by
  have hbound :=
    site_le_add_touchGraph_dist_of_margin hreach hmargin j
  omega

end YangMills.Continuum
