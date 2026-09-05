/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedState

/-!
# Finite-state resolvent factorization

The restricted weakening monomial has been converted to a finite visited
state.  The correct way to factor the complete walk sum is therefore not to
factor every walk separately and multiply two infinite sums.  Instead one
uses the second resolvent identity for the finite-state transfer operator.

This file records that noncommutative algebraic step.  If the difference of
two transfer matrices factors through a finite active-state type `kappa`,
then the complete difference of their resolvents factors through the same
type.  No cross terms are introduced.
-/

namespace YangMills.RG

noncomputable section

/-- Second resolvent identity in the orientation used by a right transfer
resolvent at the new contour and a left transfer resolvent at the base
point. -/
theorem Matrix.resolvent_sub_resolvent_eq
    {State R : Type*} [Fintype State] [DecidableEq State] [Ring R]
    (Tnew Tbase Nnew Nbase : Matrix State State R)
    (hnew : Nnew * (1 - Tnew) = 1)
    (hbase : (1 - Tbase) * Nbase = 1) :
    Nnew - Nbase =
      Nnew * (Tnew - Tbase) * Nbase := by
  calc
    Nnew - Nbase = Nnew * 1 - 1 * Nbase := by
      rw [mul_one, one_mul]
    _ = Nnew * ((1 - Tbase) * Nbase) -
        (Nnew * (1 - Tnew)) * Nbase := by
      rw [hbase, hnew]
    _ = Nnew * (Tnew - Tbase) * Nbase := by
      noncomm_ring

/-- A finite-rank transfer defect gives a factorization of the complete
resolvent defect through exactly the same intermediate type. -/
theorem Matrix.resolvent_sub_resolvent_eq_mul_mul_of_factorization
    {State kappa R : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype kappa] [DecidableEq kappa]
    [Ring R]
    (Tnew Tbase Nnew Nbase : Matrix State State R)
    (hnew : Nnew * (1 - Tnew) = 1)
    (hbase : (1 - Tbase) * Nbase = 1)
    (A : Matrix State kappa R)
    (B : Matrix kappa State R)
    (hfactor : Tnew - Tbase = A * B) :
    Nnew - Nbase =
      (Nnew * A) * (B * Nbase) := by
  rw [Matrix.resolvent_sub_resolvent_eq
    Tnew Tbase Nnew Nbase hnew hbase, hfactor]
  simp only [Matrix.mul_assoc]

end

end YangMills.RG
