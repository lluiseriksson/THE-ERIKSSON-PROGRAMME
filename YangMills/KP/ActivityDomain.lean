/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.MayerInversion

/-!
# KP activity domains — the zero-free polydisc

Upstream adoption from the satellite `lean-zero-free-regions` (the first
external consumer of this KP layer), whose first iteration identified that
the Kotecký–Preiss criterion, as formulated in `YangMills.KP.Criterion`,
reads the activity **only through its norm** and is therefore monotone under
pointwise activity domination.  Consequence: a single KP weight certifies
`Ξ ≠ 0` not at one activity but on the whole closed polydisc
`{z' : ‖z'(X)‖ ≤ ‖z(X)‖ for all X}`, and in particular on the closed unit
disc of a complex fugacity.  The fugacity section `w ↦ Ξ(w·z)` is moreover
an explicit polynomial in `w` (degree bounded by the number of polymers of
an admissible family); the satellite additionally proves it entire and keeps
the analytic-logarithm construction on its frontier.

Everything here is elementary given `partition_eq_exp_clusterSum_of_kp`
(KP2); the value is the *region* form of the nonvanishing statement, which
is what the zero-free-regions programme consumes.

References: Kotecký–Preiss (1986); Dobrushin (1996); Sokal (2001),
Proposition 2.1 and surrounding discussion of activity domains;
Friedli–Velenik (2017), Theorem 5.4.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped Classical BigOperators

/-- The same polymer combinatorics with a replaced activity. -/
def PolymerSystem.withActivity (P : PolymerSystem) (z : P.Polymer → ℂ) :
    PolymerSystem :=
  { P with activity := z }

/-- The one-complex-parameter fugacity family `w · z`. -/
def PolymerSystem.diskFamily (P : PolymerSystem) (w : ℂ) : PolymerSystem :=
  P.withActivity fun X => w * P.activity X

instance instFintypeWithActivity (P : PolymerSystem) [Fintype P.Polymer]
    (z : P.Polymer → ℂ) : Fintype (P.withActivity z).Polymer :=
  inferInstanceAs (Fintype P.Polymer)

instance instFintypeDiskFamily (P : PolymerSystem) [Fintype P.Polymer]
    (w : ℂ) : Fintype (P.diskFamily w).Polymer :=
  inferInstanceAs (Fintype P.Polymer)

variable (P : PolymerSystem) [Fintype P.Polymer]

/-- **Monotonicity of the KP criterion under activity domination.**  The
criterion reads the activity only through `‖z(Y)‖`, so any pointwise
dominated activity inherits the same weight. -/
theorem kpCriterion_withActivity_of_le {a : P.Polymer → ℝ}
    (hKP : KPCriterion P a) (z : P.Polymer → ℂ)
    (hz : ∀ X, ‖z X‖ ≤ ‖P.activity X‖) :
    KPCriterion (P.withActivity z) a := by
  obtain ⟨hnn, hsum⟩ := hKP
  refine ⟨hnn, fun X => ?_⟩
  show (∑ Y ∈ Finset.univ.filter (fun Y => P.incomp X Y),
      ‖z Y‖ * Real.exp (a Y)) ≤ a X
  refine le_trans (Finset.sum_le_sum fun Y _ => ?_) (hsum X)
  exact mul_le_mul_of_nonneg_right (hz Y) (Real.exp_pos _).le

/-- **The KP zero-free polydisc.**  One KP weight certifies `Ξ ≠ 0` for
EVERY activity dominated pointwise by that of `P`: the criterion is a
region statement, not a point statement. -/
theorem partition_withActivity_ne_zero_of_kp {a : P.Polymer → ℝ}
    (hKP : KPCriterion P a) (z : P.Polymer → ℂ)
    (hz : ∀ X, ‖z X‖ ≤ ‖P.activity X‖) :
    partition (P.withActivity z) (Finset.univ : Finset (P.withActivity z).Polymer) ≠ 0 := by
  rw [partition_eq_exp_clusterSum_of_kp (P.withActivity z)
    (kpCriterion_withActivity_of_le P hKP z hz)]
  exact Complex.exp_ne_zero _

/-- **Closed-unit-disc fugacity section of the polydisc**: `Ξ(w·z) ≠ 0` for
every `‖w‖ ≤ 1`. -/
theorem partition_diskFamily_ne_zero_of_kp {a : P.Polymer → ℝ}
    (hKP : KPCriterion P a) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    partition (P.diskFamily w) (Finset.univ : Finset (P.diskFamily w).Polymer) ≠ 0 := by
  refine partition_withActivity_ne_zero_of_kp P hKP _ fun X => ?_
  rw [norm_mul]
  calc ‖w‖ * ‖P.activity X‖ ≤ 1 * ‖P.activity X‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = ‖P.activity X‖ := one_mul _

/-- The fugacity section of the partition function is an explicit polynomial
in `w`: monomial degree = number of polymers in the admissible family. -/
theorem partition_diskFamily_eq (w : ℂ) :
    partition (P.diskFamily w) (Finset.univ : Finset (P.diskFamily w).Polymer)
      = ∑ S ∈ Finset.univ.powerset.filter (Admissible P),
          w ^ S.card * ∏ X ∈ S, P.activity X := by
  show (∑ S ∈ Finset.univ.powerset.filter (Admissible P),
      ∏ X ∈ S, (w * P.activity X)) = _
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]

end YangMills.KP
