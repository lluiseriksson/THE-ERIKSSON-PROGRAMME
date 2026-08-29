import YangMills.RG.BalabanCMP99SourceGeneratedWeightedAdjointRange

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result is not yet compiler-verified.

# Terminal-block diameter for a typed source-region chain

This module derives the intrinsic terminal-block radius for an arbitrary
typed source-region chain.  It discharges the geometric input of
`CMP99SourceActiveRegionChain.generatedCountingMass_finiteRange` internally;
no identification with the canonical iterated-lift chain is used.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N : ℕ} [NeZero d] [NeZero M] [NeZero N]

/-- Equal terminal owners force equality of every order-`M^depth` coordinate
quotient. -/
theorem CMP99SourceActiveRegionChain.div_pow_eq_of_sameTerminalBlock
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    ∀ (source target : ActiveGaugeRegion.Site Omega),
      regions.SameTerminalBlock source target →
      ∀ i : Fin d,
        (source.1 i).val / M ^ depth = (target.1 i).val / M ^ depth := by
  induction regions with
  | stop Omega =>
      intro source target hsame i
      have hst : source = target :=
        (CMP99SourceActiveRegionChain.sameTerminalBlock_stop
          (M := M) Omega source target).1 hsame
      subst target
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro source target hsame i
      have htail : tail.SameTerminalBlock
          (cmp99ActiveCoarseSiteOfFine Omega hOmega source)
          (cmp99ActiveCoarseSiteOfFine Omega hOmega target) :=
        (CMP99SourceActiveRegionChain.sameTerminalBlock_step
          (M := M) Omega hOmega tail source target).1 hsame
      have hq := ih
        (cmp99ActiveCoarseSiteOfFine Omega hOmega source)
        (cmp99ActiveCoarseSiteOfFine Omega hOmega target) htail i
      simpa only [cmp99ActiveCoarseSiteOfFine, blockSite_val,
        Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using hq

/-- Every terminal block of an arbitrary typed source-region chain has the
same literal order-`M^depth` diameter as the canonical iterated-lift chain.
No identification of the two chains is used. -/
theorem CMP99SourceActiveRegionChain.sameTerminalBlock_finBoxDist_le
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (source target : ActiveGaugeRegion.Site Omega)
    (hsame : regions.SameTerminalBlock source target) :
    finBoxDist target.1 source.1 ≤ M ^ depth - 1 := by
  unfold finBoxDist
  apply Finset.sup_le
  intro i _hi
  have hq : (source.1 i).val / M ^ depth =
      (target.1 i).val / M ^ depth :=
    regions.div_pow_eq_of_sameTerminalBlock source target hsame i
  have hpowPos : 0 < M ^ depth := pow_pos (NeZero.pos M) depth
  have hsdiv : (source.1 i).val =
      M ^ depth * ((source.1 i).val / M ^ depth) +
        (source.1 i).val % M ^ depth :=
    (Nat.div_add_mod _ _).symm
  have htdiv : (target.1 i).val =
      M ^ depth * ((target.1 i).val / M ^ depth) +
        (target.1 i).val % M ^ depth :=
    (Nat.div_add_mod _ _).symm
  have hsmodLt : (source.1 i).val % M ^ depth < M ^ depth :=
    Nat.mod_lt _ hpowPos
  have htmodLt : (target.1 i).val % M ^ depth < M ^ depth :=
    Nat.mod_lt _ hpowPos
  have hsmod : (source.1 i).val % M ^ depth ≤ M ^ depth - 1 := by
    omega
  have htmod : (target.1 i).val % M ^ depth ≤ M ^ depth - 1 := by
    omega
  rw [hq] at hsdiv
  have hkey : (source.1 i).val + (target.1 i).val % M ^ depth =
      (target.1 i).val + (source.1 i).val % M ^ depth := by
    omega
  apply finTorusDist_le_of_window
  · calc
      (target.1 i).val ≤
          (target.1 i).val + (source.1 i).val % M ^ depth :=
        Nat.le_add_right _ _
      _ = (source.1 i).val + (target.1 i).val % M ^ depth := hkey.symm
      _ ≤ (source.1 i).val + (M ^ depth - 1) :=
        Nat.add_le_add_left htmod _
  · calc
      (source.1 i).val ≤
          (source.1 i).val + (target.1 i).val % M ^ depth :=
        Nat.le_add_right _ _
      _ = (target.1 i).val + (source.1 i).val % M ^ depth := hkey
      _ ≤ (target.1 i).val + (M ^ depth - 1) :=
        Nat.add_le_add_left hsmod _

variable {Nc : ℕ} [NeZero Nc]

/-- The recursive counting mass of any typed chain has its intrinsic
terminal-block radius. -/
theorem CMP99SourceActiveRegionChain.generatedCountingMass_finiteRange_terminalBlock
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site Omega) (g := SUNLieCoord Nc)
      (regions.generatedCountingMass hd hM rho spacing epsilon background
        chain fineSmall)
      (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1) := by
  apply regions.generatedCountingMass_finiteRange
    hd hM rho spacing epsilon background chain fineSmall
  intro source target hsame
  exact regions.sameTerminalBlock_finBoxDist_le source target hsame

/-- The literal `Qprime†Qprime` mass of any typed chain inherits the same
terminal-block radius through the proved counting-mass equality. -/
theorem CMP99SourceActiveRegionChain.QprimeMass_finiteRange_terminalBlock
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := regions.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site Omega) (g := SUNLieCoord Nc)
      (T.Qprime.adjoint.comp T.Qprime)
      (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1) := by
  let T := regions.weightedQprimeTower hd hM rho spacing epsilon
    background chain fineSmall
  change FinitePiLpFiniteRange
    (ι := ActiveGaugeRegion.Site Omega) (g := SUNLieCoord Nc)
    (T.Qprime.adjoint.comp T.Qprime)
    (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1)
  rw [← regions.generatedCountingMass_eq_QprimeMass hd hM rho spacing epsilon
    background chain fineSmall]
  exact regions.generatedCountingMass_finiteRange_terminalBlock
    hd hM rho spacing epsilon background chain fineSmall

end

end YangMills.RG
