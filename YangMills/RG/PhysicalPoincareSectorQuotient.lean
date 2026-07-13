/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalPoincareWall

/-!
# The constant-sector quotient — W-2, the registered continuation of the WALL
(`hRpoly` campaign — continuation (b) of ledger Addendum 495)

W-1 (`PhysicalPoincareWall.lean`) proved that the flat block-Poincaré route
to volume-uniform CT coercivity is DEAD for `d ≥ 3`, `Nc ≥ 2`: the
direction-wise constant sector forces `L ≤ CP`.  The registered
continuation (b) asks the Poincaré question on the space where that
witness does not exist: the orthogonal complement of the constant sector
(the physical fluctuation space).  This module builds the interface and
proves everything that is TRUE TODAY, claiming nothing beyond it:

* **`constantSectorLin`** — the constant sector's inclusion packaged as a
  linear map, with **`constantSectorLin_harmonic`** recording WHY this
  sector is the dangerous one: the flat Hodge operator kills it, so only
  the block term sees it, with the wall-generating normalization;
* **`IsFluctuationCochain`** — orthogonality to every constant generator
  (`∀ v, ⟪const v, A⟫ = 0`), which is exactly orthogonality to the
  sector's span, stated WITHOUT `Submodule.orthogonal` (the `ᗮ`
  instance-resolution path whnf-times-out at this pin on the nested
  `PiLp` cochain space — measured, v1 of this module);
* **`QuotientFlatGaugeHodgePoincare`** — the Poincaré predicate restricted
  to fluctuation cochains;
* **`quotientFlatPoincare_of_flatPoincare`** — the full predicate implies
  the quotient one at the same constant (the quotient statement is
  WEAKER, hence possibly volume-uniform where the full one is not);
* **`exists_quotientFlatPoincare`** — fixed-volume non-vacuity: quotient
  constants exist at every volume;
* **`constant_not_fluctuation`** — THE NON-TRANSFER LEMMA: the W-1
  wall witness is excluded from the fluctuation space by construction
  (a nonzero constant cochain is not orthogonal to itself);
* **`VolumeUniformQuotientPoincareGate`** — the quotient gate, constant
  quantified BEFORE the volume (the Addendum-487/491 discipline);
* **`volumeUniformGate_implies_quotientGate`** — the full gate implies the
  quotient gate; since the full gate is PROVED FALSE (W-1), this
  implication carries no evidence either way about the quotient gate —
  it only certifies the weakening direction.

**Honest scope — what is deliberately NOT claimed.**  The truth value of
`VolumeUniformQuotientPoincareGate` is THE OPEN QUESTION of this lane —
neither proved nor refuted here.  `constant_not_fluctuation` removes
the W-1 WITNESS, not the possibility of a wall: slowly varying
(lowest-Fourier-mode) cochains are near-harmonic and are the registered
candidate counter-witness.  The registered next step (W-3) is the
falsifier: evaluate the quotient form on the lowest nonzero mode and
decide the gate — satisfiability proof or a second wall, either outcome
is progress.  NOT `hRpoly`, NOT the mass gap; Clay distance unchanged,
~0% (<0.1%).

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

/-! ## The constant sector, packaged -/

/-- The direction-wise constant inclusion, packaged as a linear map. -/
noncomputable def constantSectorLin (d N Nc : ℕ) [NeZero N] :
    (Fin d → SUNLieCoord Nc) →ₗ[ℝ] PhysicalGaugeOneCochain d N Nc where
  toFun v := constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v
  map_add' u v := by
    apply PiLp.ext
    intro b
    simp [constantPhysicalGaugeOneCochain_apply, PiLp.add_apply]
  map_smul' a v := by
    apply PiLp.ext
    intro b
    simp [constantPhysicalGaugeOneCochain_apply, PiLp.smul_apply]

@[simp]
theorem constantSectorLin_apply {d N Nc : ℕ} [NeZero N]
    (v : Fin d → SUNLieCoord Nc) :
    constantSectorLin d N Nc v
      = constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v := rfl

/-- The constant sector is harmonic: the flat Hodge operator kills every
generator.  This is WHY it is the dangerous sector — only the block term
sees it, with the wall-generating normalization. -/
theorem constantSectorLin_harmonic {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc] (ρ : SUNAdjointModel Nc)
    (v : Fin d → SUNLieCoord Nc) :
    flatGaugeHodgeK0CLM d N Nc ρ (constantSectorLin d N Nc v) = 0 :=
  flatGaugeHodgeK0CLM_constantPhysicalGaugeOneCochain
    (d := d) (N := N) (Nc := Nc) ρ v

/-! ## The fluctuation space, generator-wise -/

/-- A cochain is a FLUCTUATION cochain when it is orthogonal to every
direction-wise constant generator — exactly orthogonality to the constant
sector's span, stated generator-wise (the `Submodule.orthogonal` route
whnf-times-out at this pin on the nested `PiLp` space; measured). -/
def IsFluctuationCochain {d N Nc : ℕ} [NeZero N]
    (A : PhysicalGaugeOneCochain d N Nc) : Prop :=
  ∀ v : Fin d → SUNLieCoord Nc,
    (inner ℝ
      (constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v)
      A : ℝ) = 0

/-! ## The quotient Poincaré predicate -/

/-- The flat Hodge/block Poincaré predicate RESTRICTED to the fluctuation
space.  Same shape as `FlatGaugeHodgePoincare`, one extra orthogonality
hypothesis. -/
def QuotientFlatGaugeHodgePoincare
    (d L N' Nc : ℕ)
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (CP : ℝ) : Prop :=
  0 < CP ∧
    ∀ A : FinePhysicalOneCochain d L N' Nc,
      IsFluctuationCochain (d := d) (N := L * N') (Nc := Nc) A →
        ‖A‖ ^ 2 ≤
          CP *
            (inner ℝ A
                (flatGaugeHodgeK0CLM d (L * N') Nc ρ A)
              + ‖flatBlockConstraintQCLM
                    (d := d) (Nc := Nc) L N' A‖ ^ 2)

/-- The full predicate implies the quotient one at the same constant:
the quotient statement is strictly weaker, hence a volume-uniform
quotient constant is not excluded by the W-1 wall. -/
theorem quotientFlatPoincare_of_flatPoincare
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) {CP : ℝ}
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP) :
    QuotientFlatGaugeHodgePoincare d L N' Nc ρ CP :=
  ⟨hP.1, fun A _ => hP.2 A⟩

/-- Fixed-volume non-vacuity: quotient Poincaré constants exist at every
volume (restriction of the unconditional fixed-volume theorem). -/
theorem exists_quotientFlatPoincare
    (d N' Nc : ℕ) [NeZero d] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) :
    ∀ L : ℕ, ∃ CP : ℝ,
      QuotientFlatGaugeHodgePoincare d (L + 1) N' Nc ρ CP := by
  intro L
  obtain ⟨CP, hP⟩ := perVolume_flatPoincare_family d N' Nc ρ L
  exact ⟨CP, quotientFlatPoincare_of_flatPoincare ρ hP⟩

/-! ## The non-transfer lemma: the W-1 witness is excluded by construction -/

/-- **The W-1 wall witness does not live in the fluctuation space**: a
nonzero constant cochain is a constant generator, so it cannot be
orthogonal to all of them (it is not orthogonal to itself).  This removes
the WITNESS of the W-1 lower bound — it does NOT prove the quotient gate;
near-constant modes are the registered candidate counter-witness (W-3). -/
theorem constant_not_fluctuation {d N Nc : ℕ} [NeZero N]
    (v : Fin d → SUNLieCoord Nc)
    (hv : 0 < ∑ i : Fin d, ‖v i‖ ^ 2) :
    ¬ IsFluctuationCochain
        (constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v) := by
  intro hmem
  have hself := hmem v
  rw [real_inner_self_eq_norm_sq] at hself
  have hnorm :
      ‖constantPhysicalGaugeOneCochain
          (d := d) (N := N) (Nc := Nc) v‖ ^ 2
        = (N : ℝ) ^ d * ∑ i : Fin d, ‖v i‖ ^ 2 :=
    norm_sq_constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpos :
      (0 : ℝ) < ‖constantPhysicalGaugeOneCochain
          (d := d) (N := N) (Nc := Nc) v‖ ^ 2 := by
    rw [hnorm]
    exact mul_pos (pow_pos hNpos d) hv
  rw [hself] at hpos
  exact lt_irrefl 0 hpos

/-! ## The quotient gate (THE open question of this lane) -/

/-- The volume-uniform QUOTIENT Poincaré gate: one constant valid at every
volume on the fluctuation space, constant quantified BEFORE the volume.
Its truth value is neither proved nor refuted in this module — it is the
registered open question; W-3 (the lowest-mode falsifier) decides it. -/
def VolumeUniformQuotientPoincareGate
    (d N' Nc : ℕ) [NeZero d] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) : Prop :=
  ∃ CP : ℝ, 0 < CP ∧
    ∀ L : ℕ, QuotientFlatGaugeHodgePoincare d (L + 1) N' Nc ρ CP

/-- The (FALSE, by W-1) full gate implies the quotient gate.  This
certifies only the weakening direction; it carries no evidence about the
quotient gate's truth value. -/
theorem volumeUniformGate_implies_quotientGate
    {d N' Nc : ℕ} [NeZero d] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (h : VolumeUniformFlatPoincareGate d N' Nc ρ) :
    VolumeUniformQuotientPoincareGate d N' Nc ρ := by
  obtain ⟨CP, hCP, hall⟩ := h
  exact ⟨CP, hCP, fun L =>
    quotientFlatPoincare_of_flatPoincare ρ (hall L)⟩

end YangMills.RG
