import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse
import YangMills.RG.BalabanCMP99SourceFlatQprimeBlockOffsetEquiv
import YangMills.RG.NeumannGeneratedIntegerCountingKernel
import YangMills.RG.NeumannIntegerBlockImageAverage

/-!
PRE-VALIDATION: source present, .olean not materialized; not compiler verified.

R2d.2b: the canonical iterated lift contains a WHOLE terminal block for every
active coarse owner. This is proved from the recursive lift, not assumed for
an arbitrary truncated active region. The offset equivalence is composed
with the existing cmp99BlockOffsetEquiv. Its integer coordinates are literal
B*y+r with B=M^depth; finite-sum reindexing introduces no B^d multiplier.

This carrier dictionary is not an inverse, an l2 extension, a physical B0
bound, or attainment of window15. It does not change 20/41 or TermSource0.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {d M N : ℕ} [NeZero d] [NeZero M] [NeZero N]

/-- Exact membership in the recursively constructed complete-block lift. -/
theorem neumann_mem_iteratedLift_iff_terminalOwner
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) :
    x ∈ (cmp99IteratedLiftActiveRegion (M := M) Omega depth).sites ↔
      cmp99GeneratedTerminalBlockSite M N depth x ∈ Omega.sites := by
  induction depth generalizing x with
  | zero => simpa only [cmp99IteratedLiftActiveRegion_zero,
      cmp99GeneratedTerminalBlockSite_zero]
  | succ depth ih =>
      rw [cmp99IteratedLiftActiveRegion_succ,
        mem_cmp99LiftActiveRegion_sites_iff,
        cmp99GeneratedTerminalBlockSite_succ]
      exact ih (blockSite M (cmp99RegionalLatticeSize M N depth) x)

/-- The one-block carrier and the actual active terminal fibre coincide.
The active membership witness is produced internally from the lifted region. -/
def neumannGeneratedBlockSitesToActiveFibre
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (y : ActiveGaugeRegion.Site Omega) :
    {x : FinBox d (M ^ depth * N) // x ∈ blockOf (M ^ depth) N y.1} ≃
      {x : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth) //
        cmp99GeneratedTerminalBlockSite M N depth x.1 = y.1} where
  toFun x := by
    let e := cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth
    have ho : cmp99GeneratedTerminalBlockSite M N depth (e.symm x.1) = y.1 := by
      rw [cmp99GeneratedTerminalBlockSite_eq_blockSite_pow]
      change blockSite (M ^ depth) N (e (e.symm x.1)) = y.1
      rw [e.apply_symm_apply]
      exact (mem_blockOf (M ^ depth) N y.1 x.1).mp x.2
    exact ⟨⟨e.symm x.1, (neumann_mem_iteratedLift_iff_terminalOwner
      Omega depth (e.symm x.1)).mpr (ho.symm ▸ y.2)⟩, ho⟩
  invFun x := ⟨cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth x.1.1,
    (mem_blockOf (M ^ depth) N y.1 _).mpr
      ((cmp99GeneratedTerminalBlockSite_eq_blockSite_pow depth x.1.1).symm.trans x.2)⟩
  left_inv x := by
    apply Subtype.ext
    exact (cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth).apply_symm_apply x.1
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth).symm_apply_apply x.1.1

/-- The complete M^depth offset box, not a supplied fibre bijection. -/
def neumannGeneratedCompleteFibreOffsetEquiv
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (y : ActiveGaugeRegion.Site Omega) :
    FinBox d (M ^ depth) ≃
      {x : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth) //
        cmp99GeneratedTerminalBlockSite M N depth x.1 = y.1} :=
  (cmp99BlockOffsetEquiv y.1).trans
    (neumannGeneratedBlockSitesToActiveFibre Omega depth y)

/-- The constructed active-site map has the literal integer block coordinates. -/
theorem neumannGeneratedCompleteFibreOffsetEquiv_integerCoordinates
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (y : ActiveGaugeRegion.Site Omega) (r : FinBox d (M ^ depth)) :
    neumannFiniteSiteIntegerCoordinates
      (neumannGeneratedCompleteFibreOffsetEquiv Omega depth y r).1.1 =
      neumannIntegerFineBlockPoint (neumannFiniteSiteIntegerCoordinates y.1) r := by
  let e := cmp99GeneratedFineBoxOneBlockEquiv (d := d) M N depth
  have hv (mu : Fin d) :
      ((e.symm (cmp99BlockEmbed y.1 r)) mu).val = (cmp99BlockEmbed y.1 r mu).val := by
    have h := cmp99GeneratedFineBoxOneBlockEquiv_apply_val
      M N depth (e.symm (cmp99BlockEmbed y.1 r)) mu
    change (e (e.symm (cmp99BlockEmbed y.1 r)) mu).val = _ at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  funext mu
  change (((e.symm (cmp99BlockEmbed y.1 r) mu).val : ℕ) : ℤ) =
    ((M ^ depth : ℕ) : ℤ) * ((y.1 mu).val : ℤ) + ((r mu).val : ℤ)
  rw [hv]
  simp only [cmp99BlockEmbed, Nat.cast_add, Nat.cast_mul]

/-- Reindex the actual active fibre without inserting a counting factor. -/
theorem sum_neumannGeneratedCompleteFibre_eq_offsets
    {V : Type*} [AddCommMonoid V]
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (y : ActiveGaugeRegion.Site Omega)
    (f : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth) → V) :
    (∑ x : {x : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth) //
      cmp99GeneratedTerminalBlockSite M N depth x.1 = y.1}, f x.1) =
      ∑ r : FinBox d (M ^ depth),
        f (neumannGeneratedCompleteFibreOffsetEquiv Omega depth y r).1 := by
  exact ((neumannGeneratedCompleteFibreOffsetEquiv Omega depth y).sum_comp
    (fun x => f x.1)).symm

#print axioms neumann_mem_iteratedLift_iff_terminalOwner
#print axioms neumannGeneratedBlockSitesToActiveFibre
#print axioms neumannGeneratedCompleteFibreOffsetEquiv
#print axioms neumannGeneratedCompleteFibreOffsetEquiv_integerCoordinates
#print axioms sum_neumannGeneratedCompleteFibre_eq_offsets

end
end YangMills.RG
