import YangMills.RG.NeumannHalfCellBlockReflection
import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse
import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanion

/-!
PRE-VALIDATION: source present, no draft .olean materialized; not compiler
verified. This constructs reflection on the canonical FULL lifted carrier
and targets the literal flat generated counting-adjoint mass kernel.
No invariant arbitrary active region, regional Green equality, or derivative
B0 is assumed or concluded. The coefficient remains (M^-d)^(2*depth), not
the different source-weighted-adjoint coefficient (M^-d)^depth.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

private theorem fullLift_mem (depth : ℕ) :
    ∀ x : FinBox d (cmp99RegionalLatticeSize M N depth),
      x ∈ (cmp99IteratedLiftActiveRegion (M := M)
        (cmp99SourceFullActiveRegion d N) depth).sites := by
  induction depth with
  | zero =>
      intro x
      exact Finset.mem_univ x
  | succ depth ih =>
      intro x
      rw [cmp99IteratedLiftActiveRegion_succ, mem_cmp99LiftActiveRegion_sites_iff]
      exact ih (blockSite M (cmp99RegionalLatticeSize M N depth) x)

/-- The reflected point is constructed inside the full lifted carrier.
There is no caller-supplied site permutation or invariance certificate. -/
def neumannGeneratedFullSiteReflectionDraft
    (depth : ℕ) (branch : Fin d → Bool)
    (x : ActiveGaugeRegion.Site (cmp99IteratedLiftActiveRegion (M := M)
      (cmp99SourceFullActiveRegion d N) depth)) :
    ActiveGaugeRegion.Site (cmp99IteratedLiftActiveRegion (M := M)
      (cmp99SourceFullActiveRegion d N) depth) :=
  ⟨neumannHalfCellReflection branch x.1, fullLift_mem depth _⟩

theorem neumannGeneratedFullSiteReflectionDraft_involutive
    (depth : ℕ) (branch : Fin d → Bool) :
    Function.Involutive
      (neumannGeneratedFullSiteReflectionDraft (M := M) (N := N) depth branch) := by
  intro x
  apply Subtype.ext
  exact neumannHalfCellReflection_involutive branch x.1

private theorem finBoxCast_reflection {A B : ℕ} (h : A = B)
    (branch : Fin d → Bool) (x : FinBox d A) :
    Equiv.cast (congrArg (FinBox d) h) (neumannHalfCellReflection branch x) =
      neumannHalfCellReflection branch (Equiv.cast (congrArg (FinBox d) h) x) := by
  subst B
  rfl

theorem neumannGeneratedTerminalOwner_reflection_draft
    (depth : ℕ) (branch : Fin d → Bool)
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) :
    cmp99GeneratedTerminalBlockSite M N depth (neumannHalfCellReflection branch x) =
      neumannHalfCellReflection branch (cmp99GeneratedTerminalBlockSite M N depth x) := by
  rw [cmp99GeneratedTerminalBlockSite_eq_blockSite_pow,
    cmp99GeneratedTerminalBlockSite_eq_blockSite_pow]
  have he := finBoxCast_reflection
    (cmp99RegionalLatticeSize_eq_pow_mul M N depth) branch x
  change cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth
      (neumannHalfCellReflection branch x) =
    neumannHalfCellReflection branch
      (cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth x) at he
  rw [he]
  exact blockSite_neumannHalfCellReflection branch _

/-- Literal generated counting mass, simultaneously reflected input/output.
This is an equality on every Lie-coordinate probe, not an orientation bound
and not an identification with the retained physical precision. -/
theorem neumannGeneratedFullCountingMass_reflection_draft
    (depth : ℕ) (branch : Fin d → Bool) :
    let Omega := cmp99SourceFullActiveRegion d N
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
    ∀ (source target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (v : SUNLieCoord Nc),
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
          (regions.flatExplicitQprime (Nc := Nc)))
        (singleFinitePiLp (neumannGeneratedFullSiteReflectionDraft depth branch source) v)
        (neumannGeneratedFullSiteReflectionDraft depth branch target) =
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
          (regions.flatExplicitQprime (Nc := Nc)))
        (singleFinitePiLp source v) target := by
  dsimp only
  intro source target v
  rw [cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply,
    cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply]
  change (if cmp99GeneratedTerminalBlockSite M N depth
      (neumannHalfCellReflection branch target.1) =
    cmp99GeneratedTerminalBlockSite M N depth
      (neumannHalfCellReflection branch source.1) then
      (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) • v else 0) = _
  rw [neumannGeneratedTerminalOwner_reflection_draft,
    neumannGeneratedTerminalOwner_reflection_draft]
  exact if_congr (neumannHalfCellReflection_involutive branch).injective.eq_iff rfl rfl

end

end YangMills.RG

#print axioms YangMills.RG.neumannGeneratedFullSiteReflectionDraft_involutive
#print axioms YangMills.RG.neumannGeneratedTerminalOwner_reflection_draft
#print axioms YangMills.RG.neumannGeneratedFullCountingMass_reflection_draft
