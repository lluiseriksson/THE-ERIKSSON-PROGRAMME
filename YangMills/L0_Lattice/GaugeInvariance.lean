import YangMills.L0_Lattice.WilsonAction

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic

open scoped BigOperators

namespace YangMills

variable {d N : ℕ} {G : Type _}
variable [Group G] [FiniteLatticeGeometry d N G]

/--
Gauge invariance of the abstract Wilson action:
if the plaquette energy is invariant under conjugation, then the action is gauge invariant.
-/
theorem wilsonAction_gaugeInvariant
    (plaquetteEnergy : G → ℝ)
    (hconj : ConjInvariant plaquetteEnergy)
    (u : GaugeTransform d N G)
    (A : GaugeConfig d N G) :
    wilsonAction plaquetteEnergy (GaugeConfig.gaugeAct u A) =
      wilsonAction plaquetteEnergy A := by
  classical
  unfold wilsonAction
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [GaugeConfig.plaquetteHolonomy_gaugeAct]
  exact hconj _ _

end YangMills
