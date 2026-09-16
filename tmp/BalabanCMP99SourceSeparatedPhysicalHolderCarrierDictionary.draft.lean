/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H5e1: explicit transport from D4's `ell*(2*(K*Q))` carrier to CMP99's
definitionally different separated presentation.  Shift, physical-bond target
and localization owner are proved propositionally.  No metric estimate, B0,
window-15 claim or terminal field is asserted.
-/

import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge
import YangMills.RG.BalabanCMP116CMP89PhysicalBondDisplacementDictionary

namespace YangMills.RG

noncomputable section

/-- A dependent carrier cast commutes with the positive periodic step. -/
theorem finBoxEquivCast_shift_draft
    {d A B : ℕ} [NeZero A] [NeZero B]
    (h : A = B) (x : FinBox d A) (mu : Fin d) :
    Equiv.cast (congrArg (FinBox d) h) (x.shift mu) =
      (Equiv.cast (congrArg (FinBox d) h) x).shift mu := by
  subst B
  rfl

/-- D4 fine sites presented on the separated CMP99 carrier. -/
def cmp99SourceSeparatedFineSiteOfD4_draft
    (L K Q depth : ℕ)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) :
    FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth).symm x

/-- The separated presentation preserves the literal positive target step. -/
theorem cmp99SourceSeparatedFineSiteOfD4_shift_draft
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) (mu : Fin 4) :
    cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth (x.shift mu) =
      (cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth x).shift mu := by
  unfold cmp99SourceSeparatedFineSiteOfD4_draft
    cmp99Eq389SourceLocalizationSiteEquiv
  exact finBoxEquivCast_shift_draft
    (cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier
      L K Q depth).symm x mu

/-- The physical bond target commutes with the carrier presentation; the bond
direction is unchanged. -/
theorem cmp116BondTarget_sourceSeparatedFineSiteOfD4_draft
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) (mu : Fin 4) :
    cmp116BondTarget
        (cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth x, mu) =
      cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth (x.shift mu) := by
  exact (cmp99SourceSeparatedFineSiteOfD4_shift_draft
    L K Q depth x mu).symm

/-- The owner of the transported canonical block basepoint is exactly the D4
coarse site.  This equality closes the owner side of the carrier dictionary. -/
theorem
    cmp99Eq389SourceLocalizationOwner_sourceSeparatedFineSiteOfD4_blockBasepoint_draft
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (y : FinBox 4 (2 * (K * Q))) :
    cmp99Eq389SourceLocalizationOwner L K Q depth
        (cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth
          (blockBasepoint (L ^ (depth + 1)) (2 * (K * Q)) y)) = y := by
  unfold cmp99Eq389SourceLocalizationOwner
    cmp99SourceSeparatedFineSiteOfD4_draft
  rw [Equiv.apply_symm_apply]
  exact blockSite_blockBasepoint _ _ y

end

end YangMills.RG
