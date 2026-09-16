/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel

/-!
# Collapse of the generated terminal owner to one physical block

On the canonical full flat tower, `depth` successive order-`M` block maps have
the same owner as the single literal order-`M^depth` block map.  This file
states that identification through an explicit finite-box equivalence and
keeps the normalization identity

`(M^{-d})^depth = (M^depth)^{-d}`

separate from the carrier dictionary.  The final kernel statement rewrites
the generated counting mass using the one-block owner without identifying a
CMP99 stratum, a precision, an inverse or a Green operator.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The closed-form generated fine side as an explicit one-block fine side. -/
def cmp99GeneratedFineBoxOneBlockEquiv (M N depth : ℕ) :
    FinBox d (cmp99RegionalLatticeSize M N depth) ≃
      FinBox d (M ^ depth * N) :=
  Equiv.cast (congrArg (FinBox d)
    (cmp99RegionalLatticeSize_eq_pow_mul M N depth))

omit [NeZero d] in
private theorem finBox_cast_apply_val
    {A B : ℕ} (h : A = B) (x : FinBox d A) (i : Fin d) :
    ((Equiv.cast (congrArg (FinBox d) h) x) i).val = (x i).val := by
  subst h
  rfl

omit [NeZero d] [NeZero M] [NeZero N] [NeZero Nc] in
@[simp] theorem cmp99GeneratedFineBoxOneBlockEquiv_apply_val
    (M N depth : ℕ)
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) (i : Fin d) :
    ((cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N depth x) i).val = (x i).val := by
  exact finBox_cast_apply_val
    (cmp99RegionalLatticeSize_eq_pow_mul M N depth) x i

omit [NeZero d] in
/-- The recursively generated terminal owner is the literal one-block owner
with block side `M^depth`. -/
theorem cmp99GeneratedTerminalBlockSite_eq_blockSite_pow
    (depth : ℕ)
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) :
    cmp99GeneratedTerminalBlockSite M N depth x =
      blockSite (M ^ depth) N
        (cmp99GeneratedFineBoxOneBlockEquiv
          (d := d) M N depth x) := by
  funext i
  apply Fin.ext
  simp only [cmp99GeneratedTerminalBlockSite, blockSite_val,
    cmp99GeneratedFineBoxOneBlockEquiv_apply_val]

/-- The product of the `depth` one-scale averaging weights is exactly the
single order-`M^depth` averaging weight. -/
theorem cmp99SourceBlockAverageWeight_pow_eq_oneBlock
    (M d depth : ℕ) :
    (cmp99SourceBlockAverageWeight M d) ^ depth =
      cmp99SourceBlockAverageWeight (M ^ depth) d := by
  unfold cmp99SourceBlockAverageWeight
  rw [Nat.cast_pow, inv_pow, ← pow_mul, ← pow_mul,
    Nat.mul_comm depth d]

/-- The generated counting-mass coefficient is the square of the one-block
source weight. -/
theorem cmp99SourceBlockAverageWeight_two_mul_eq_oneBlock_sq
    (M d depth : ℕ) :
    (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) =
      (cmp99SourceBlockAverageWeight (M ^ depth) d) ^ 2 := by
  rw [← cmp99SourceBlockAverageWeight_pow_eq_oneBlock]
  rw [← pow_mul, Nat.mul_comm 2 depth]

/-- Exact one-block-owner form of the canonical generated counting-mass
kernel.  No full-fibre cardinality or stratum identification is used. -/
theorem cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply_oneBlock
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
    ∀ (source target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (v : SUNLieCoord Nc),
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
          (regions.flatExplicitQprime (Nc := Nc)))
            (singleFinitePiLp source v) target =
        if blockSite (M ^ depth) N
              (cmp99GeneratedFineBoxOneBlockEquiv
                (d := d) M N depth target.1) =
            blockSite (M ^ depth) N
              (cmp99GeneratedFineBoxOneBlockEquiv
                (d := d) M N depth source.1) then
          (cmp99SourceBlockAverageWeight (M ^ depth) d) ^ 2 • v
        else 0 := by
  dsimp only
  intro source target v
  rw [cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply]
  rw [cmp99GeneratedTerminalBlockSite_eq_blockSite_pow,
    cmp99GeneratedTerminalBlockSite_eq_blockSite_pow,
    cmp99SourceBlockAverageWeight_two_mul_eq_oneBlock_sq]

end

end YangMills.RG
