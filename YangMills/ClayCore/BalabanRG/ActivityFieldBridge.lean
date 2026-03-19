import Mathlib
import YangMills.ClayCore.BalabanRG.ActivitySpaceNorms
import YangMills.ClayCore.BalabanRG.BalabanFieldSpace
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ActivityFieldBridge — Layer 15D (v0.9.5)

Abstract interface bridging ActivityFamily (Polymer-based) and
Lattice Fields (Site-based). No concrete implementation yet.
-/

noncomputable section

/-- A Bridge: abstract mapping from activities to lattice field configurations. -/
structure ActivityFieldBridge (d k : ℕ) where
  /-- Maps each activity K to a field configuration on BalabanLatticeSite. -/
  fieldOfActivity : ActivityFamily d k → (BalabanLatticeSite d k → ℝ)
  /-- Zero activity maps to zero field. -/
  zero_field : fieldOfActivity (fun _ => 0) = fun _ => 0

variable {d k : ℕ}

/-- The field support of an activity through the bridge. -/
def inducedFieldSupport (bridge : ActivityFieldBridge d k)
    (K : ActivityFamily d k) :
    Finset (BalabanLatticeSite d k) :=
  balabanFieldSupport (bridge.fieldOfActivity K)

/-- The large-field region induced by activity K at threshold t. -/
def inducedLargeFieldRegion (bridge : ActivityFieldBridge d k)
    (K : ActivityFamily d k) (t : ℝ) :
    Finset (BalabanLatticeSite d k) :=
  balabanLargeFieldRegion (bridge.fieldOfActivity K) t

/-- The small-field region induced by activity K at threshold t. -/
def inducedSmallFieldRegion (bridge : ActivityFieldBridge d k)
    (K : ActivityFamily d k) (t : ℝ) :
    Finset (BalabanLatticeSite d k) :=
  balabanSmallFieldRegion (bridge.fieldOfActivity K) t

/-- Zero activity has empty induced support. 0 sorrys. -/
theorem inducedFieldSupport_zero (bridge : ActivityFieldBridge d k) :
    inducedFieldSupport bridge (fun _ => 0) = ∅ := by
  unfold inducedFieldSupport balabanFieldSupport
  rw [bridge.zero_field]; simp

/-- Large ∪ small = univ. 0 sorrys. -/
theorem inducedSmallLargePartition (bridge : ActivityFieldBridge d k)
    (K : ActivityFamily d k) (β : ℝ) :
    inducedLargeFieldRegion bridge K (fieldThreshold β) ∪
    inducedSmallFieldRegion bridge K (fieldThreshold β) = Finset.univ :=
  balabanLargeSmallPartition (bridge.fieldOfActivity K) (fieldThreshold β)

/-- Large ∩ small = ∅. 0 sorrys. -/
theorem inducedSmallLargeDisjoint (bridge : ActivityFieldBridge d k)
    (K : ActivityFamily d k) (β : ℝ) :
    Disjoint
      (inducedLargeFieldRegion bridge K (fieldThreshold β))
      (inducedSmallFieldRegion bridge K (fieldThreshold β)) :=
  balabanLargeSmallDisjoint (bridge.fieldOfActivity K) (fieldThreshold β)

/-- Small-field predicate for activities via bridge. -/
def SmallFieldPredViaBridge (bridge : ActivityFieldBridge d k)
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (K : ActivityFamily d k) : Prop :=
  SmallFieldPredicateField d N_c k β (bridge.fieldOfActivity K)

/-- Large-field predicate for activities via bridge. -/
def LargeFieldPredViaBridge (bridge : ActivityFieldBridge d k)
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (K : ActivityFamily d k) : Prop :=
  LargeFieldPredicateField d N_c k β (bridge.fieldOfActivity K)

/-- Every activity is either small or large. 0 sorrys. -/
theorem small_or_large_via_bridge (bridge : ActivityFieldBridge d k)
    (N_c : ℕ) [NeZero N_c] (β : ℝ) (K : ActivityFamily d k) :
    SmallFieldPredViaBridge bridge N_c β K ∨
    LargeFieldPredViaBridge bridge N_c β K := by
  simpa [SmallFieldPredViaBridge, LargeFieldPredViaBridge] using
    small_or_large_field d N_c k β (bridge.fieldOfActivity K)

/-- SmallField via bridge iff all induced sites below threshold. 0 sorrys. -/
theorem smallPred_via_bridge_iff (bridge : ActivityFieldBridge d k)
    (N_c : ℕ) [NeZero N_c] (β : ℝ) (K : ActivityFamily d k) :
    SmallFieldPredViaBridge bridge N_c β K ↔
      ∀ x : BalabanLatticeSite d k,
        |bridge.fieldOfActivity K x| < fieldThreshold β := by
  simpa [SmallFieldPredViaBridge] using
    smallField_iff (d := d) (N_c := N_c) (k := k) (β := β) (bridge.fieldOfActivity K)

/-- Zero activity is small for any β. 0 sorrys. -/
theorem zero_activity_small (bridge : ActivityFieldBridge d k)
    (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    SmallFieldPredViaBridge bridge N_c β (fun _ => 0) := by
  rw [smallPred_via_bridge_iff]
  intro x
  rw [bridge.zero_field]
  simp [fieldThreshold_pos β]

end

end YangMills.ClayCore
