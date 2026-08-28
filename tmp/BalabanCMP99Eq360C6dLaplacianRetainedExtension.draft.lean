import YangMills.RG.BalabanCMP99Eq335PhysicalRetainedNearIdentity
import YangMills.RG.BalabanCMP99Eq335PhysicalLaplacianInternalCarrier
import YangMills.RG.BalabanCMP99SourceLocalizedRetainedTower

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# One canonical extension for both the retained average and the Laplacian

The original retained extension keeps only the bonds read by the recursive
`Qprime` tower.  The literal C6d Laplacian also reads every internal bond of
the active region.  This module constructs the minimal union extension,
proves that it leaves both objects unchanged, and never assumes an equality
between independently chosen operators.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable {Omega : ActiveGaugeRegion d N}

/-- Canonical identity extension on the exact union of the recursive
`Qprime` read carrier and the internal bonds read by the regional
Laplacian. -/
noncomputable def cmp99Eq360C6dLaplacianRetainedExtension
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (background : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeBackground d N Nc := by
  classical
  exact gaugeConfigOfPositiveBonds fun b =>
    if b ∈ regions.retainedFineReadBonds (Nc := Nc) ∪ Omega.bonds then
      background (positiveEdgeOfPhysicalBond b)
    else 1

@[simp] theorem cmp99Eq360C6dLaplacianRetainedExtension_apply_pos_of_mem
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (background : PhysicalGaugeBackground d N Nc)
    (b : PhysicalBond d N)
    (hb : b ∈ regions.retainedFineReadBonds (Nc := Nc) ∪ Omega.bonds) :
    cmp99Eq360C6dLaplacianRetainedExtension regions background
        (positiveEdgeOfPhysicalBond b) =
      background (positiveEdgeOfPhysicalBond b) := by
  classical
  rw [cmp99Eq360C6dLaplacianRetainedExtension,
    gaugeConfigOfPositiveBonds_apply_pos, if_pos hb]

/-- Local bounds on the two literal read families become global smallness
of the union extension. -/
theorem norm_cmp99Eq360C6dLaplacianRetainedExtension_sub_one_le
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (background : PhysicalGaugeBackground d N Nc)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hretained : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hlaplacian : ∀ q ∈ Omega.bonds,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ∀ e : ConcreteEdge d N,
      ‖(cmp99Eq360C6dLaplacianRetainedExtension regions background e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon := by
  intro e
  rcases e with ⟨y, mu, orient⟩
  cases orient with
  | false =>
      rw [cmp99Eq360C6dLaplacianRetainedExtension,
        gaugeConfigOfPositiveBonds_apply_neg]
      exact (norm_sun_inv_sub_one_le _).trans (by
        by_cases hb : (y, mu) ∈
            regions.retainedFineReadBonds (Nc := Nc) ∪ Omega.bonds
        · rw [if_pos hb]
          rcases Finset.mem_union.mp hb with hq | hq
          · exact hretained (y, mu) hq
          · exact hlaplacian (y, mu) hq
        · rw [if_neg hb]
          simpa using hepsilon)
  | true =>
      change ‖(cmp99Eq360C6dLaplacianRetainedExtension regions background
          (positiveEdgeOfPhysicalBond (y, mu)) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon
      by_cases hb : (y, mu) ∈
          regions.retainedFineReadBonds (Nc := Nc) ∪ Omega.bonds
      · rw [cmp99Eq360C6dLaplacianRetainedExtension_apply_pos_of_mem
          regions background (y, mu) hb]
        rcases Finset.mem_union.mp hb with hq | hq
        · exact hretained (y, mu) hq
        · exact hlaplacian (y, mu) hq
      · rw [cmp99Eq360C6dLaplacianRetainedExtension,
          gaugeConfigOfPositiveBonds_apply_pos, if_neg hb]
        simpa using hepsilon

/-- The union extension preserves the literal regional Laplacian because it
retains every internal bond of the active region. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_eq_laplacianRetainedExtension
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (rho : SUNAdjointModel Nc)
    (background : PhysicalGaugeBackground d N Nc) (spacing : ℝ) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega rho background spacing =
      cmp99ActiveRegionSourceCovariantLaplacian Omega rho
        (cmp99Eq360C6dLaplacianRetainedExtension regions background)
        spacing := by
  apply cmp99ActiveRegionSourceCovariantLaplacian_eq_of_eqOn_internalBonds
  intro b hb
  exact (cmp99Eq360C6dLaplacianRetainedExtension_apply_pos_of_mem
    regions background b (Finset.mem_union_right _ hb)).symm

/-- The original retained extension and the Laplacian-aware extension agree
on the exact recursive carrier, hence their terminal `Qprime` operators are
heterogeneously equal.  This is the only tower transport used downstream. -/
theorem cmp99Eq360C6d_retainedFineExtension_Qprime_heq_laplacianExtension
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : PhysicalGaugeBackground d N Nc)
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (hretained : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hlaplacian : ∀ q ∈ Omega.bonds,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let U := regions.retainedFineExtension background
    let hU := regions.norm_retainedFineExtension_sub_one_le background epsilon
      chain.epsilon_nonneg hretained
    let V := cmp99Eq360C6dLaplacianRetainedExtension regions background
    let hV := norm_cmp99Eq360C6dLaplacianRetainedExtension_sub_one_le
      regions background epsilon chain.epsilon_nonneg hretained hlaplacian
    HEq
      (regions.weightedQprimeTower hd hM rho spacing epsilon U chain hU).Qprime
      (regions.weightedQprimeTower hd hM rho spacing epsilon V chain hV).Qprime := by
  dsimp only
  apply cmp99SourceWeightedQprimeTower_Qprime_heq_of_eqOn_retainedFineReadBonds
  intro q hq
  rw [regions.retainedFineExtension_apply_pos_of_mem background q hq,
    cmp99Eq360C6dLaplacianRetainedExtension_apply_pos_of_mem
      regions background q (Finset.mem_union_left _ hq)]

/-- A Laplacian equality and a heterogeneous equality of the terminal
averages determine the same endomorphism-valued precision.  This is pure
dependent transport; it adds no analytic hypothesis. -/
theorem cmp99SourceGaugePrecision_eq_of_laplacian_eq_of_Qprime_heq
    {E F F' : CMP99SourceWeightedTowerHilbertSpace}
    (Delta Delta' : E.carrier →L[ℝ] E.carrier)
    (Q : E.carrier →L[ℝ] F.carrier)
    (Q' : E.carrier →L[ℝ] F'.carrier) (a : ℝ)
    (hDelta : Delta = Delta') (hF : F = F') (hQ : HEq Q Q') :
    cmp99SourceGaugePrecision Delta Q a =
      cmp99SourceGaugePrecision Delta' Q' a := by
  subst Delta'
  subst F'
  exact congrArg (fun R => cmp99SourceGaugePrecision Delta R a)
    (eq_of_heq hQ)

end

end YangMills.RG
