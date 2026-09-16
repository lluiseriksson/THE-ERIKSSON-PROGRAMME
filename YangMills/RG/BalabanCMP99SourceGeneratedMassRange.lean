/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedMassTransition
import YangMills.RG.BalabanCMP99SourcePi4Collar
import YangMills.RG.FinitePiLpCombesThomas

/-!
# Finite range of the generated CMP99 averaging mass

The literal multiscale average `Q'_j` only sees the terminal order-`M^j`
block.  This file exposes that fact without replacing the generated operator
by an abstract finite-range kernel.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Closed form of the recursively generated lattice side. -/
theorem cmp99RegionalLatticeSize_eq_pow_mul (M N depth : ℕ) :
    cmp99RegionalLatticeSize M N depth = M ^ depth * N := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      simp only [cmp99RegionalLatticeSize_succ, ih, pow_succ]
      ac_rfl

/-- Terminal owner of a fine site after `depth` literal order-`M` blockings. -/
def cmp99GeneratedTerminalBlockSite (M N depth : ℕ) [NeZero M] [NeZero N]
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) : FinBox d N :=
  fun i => ⟨(x i).val / M ^ depth, by
    apply Nat.div_lt_of_lt_mul
    simpa [cmp99RegionalLatticeSize_eq_pow_mul] using (x i).isLt⟩

@[simp] theorem cmp99GeneratedTerminalBlockSite_zero
    (x : FinBox d N) :
    cmp99GeneratedTerminalBlockSite M N 0 x = x := by
  funext i
  apply Fin.ext
  simp [cmp99GeneratedTerminalBlockSite]

/-- One literal block step followed by the remaining terminal-owner map is
the direct terminal owner. -/
theorem cmp99GeneratedTerminalBlockSite_succ
    (depth : ℕ)
    (x : FinBox d (cmp99RegionalLatticeSize M N (depth + 1))) :
    cmp99GeneratedTerminalBlockSite M N (depth + 1) x =
      cmp99GeneratedTerminalBlockSite M N depth
        (blockSite M (cmp99RegionalLatticeSize M N depth) x) := by
  funext i
  apply Fin.ext
  simp only [cmp99GeneratedTerminalBlockSite, blockSite_val]
  rw [Nat.div_div_eq_div_mul]
  congr 1
  rw [pow_succ]
  exact Nat.mul_comm _ _

/-- Two sites with the same generated terminal owner lie in one literal
order-`M^depth` block. -/
theorem finBoxDist_le_of_same_generatedTerminalBlock
    (depth : ℕ)
    (x y : FinBox d (cmp99RegionalLatticeSize M N depth))
    (howner : cmp99GeneratedTerminalBlockSite M N depth x =
      cmp99GeneratedTerminalBlockSite M N depth y) :
    finBoxDist x y ≤ M ^ depth - 1 := by
  unfold finBoxDist
  apply Finset.sup_le
  intro i _hi
  have hq : (x i).val / M ^ depth = (y i).val / M ^ depth := by
    have hi := congrFun howner i
    exact congrArg Fin.val hi
  have hL : 0 < M ^ depth := pow_pos (NeZero.pos M) depth
  have hxdiv : (x i).val = M ^ depth * ((x i).val / M ^ depth) +
      (x i).val % M ^ depth := (Nat.div_add_mod _ _).symm
  have hydiv : (y i).val = M ^ depth * ((y i).val / M ^ depth) +
      (y i).val % M ^ depth := (Nat.div_add_mod _ _).symm
  have hxmod : (x i).val % M ^ depth < M ^ depth := Nat.mod_lt _ hL
  have hymod : (y i).val % M ^ depth < M ^ depth := Nat.mod_lt _ hL
  have hxmodLe : (x i).val % M ^ depth ≤ M ^ depth - 1 := by omega
  have hymodLe : (y i).val % M ^ depth ≤ M ^ depth - 1 := by omega
  rw [hq] at hxdiv
  have hkey : (x i).val + (y i).val % M ^ depth =
      (y i).val + (x i).val % M ^ depth := by
    omega
  apply finTorusDist_le_of_window
  · calc
      (x i).val ≤ (x i).val + (y i).val % M ^ depth := Nat.le_add_right _ _
      _ = (y i).val + (x i).val % M ^ depth := hkey
      _ ≤ (y i).val + (M ^ depth - 1) := Nat.add_le_add_left hxmodLe _
  · calc
      (y i).val ≤ (y i).val + (x i).val % M ^ depth := Nat.le_add_right _ _
      _ = (x i).val + (y i).val % M ^ depth := hkey.symm
      _ ≤ (x i).val + (M ^ depth - 1) := Nat.add_le_add_left hymodLe _

/-- The active coarse site owned by one fine site of a block-saturated
region. -/
def cmp99ActiveCoarseSiteOfFine
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (x : ActiveGaugeRegion.Site Omega) :
    ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) :=
  ⟨blockSite M N' x.1,
    (mem_cmp99ActiveCoarseRegion_sites_iff
      (M := M) (N' := N') Omega (blockSite M N' x.1)).2
        (hOmega x.1 x.2)⟩

/-- Recursive equivalence relation saying that two active sites arrive at
the same terminal site of a typed physical region chain. -/
def CMP99SourceActiveRegionChain.SameTerminalBlock
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    ActiveGaugeRegion.Site Omega → ActiveGaugeRegion.Site Omega → Prop := by
  intro source target
  induction regions with
  | stop Omega => exact source = target
  | @step N' depth _ Omega hOmega tail ih =>
      exact ih (cmp99ActiveCoarseSiteOfFine Omega hOmega source)
        (cmp99ActiveCoarseSiteOfFine Omega hOmega target)

@[simp] theorem CMP99SourceActiveRegionChain.sameTerminalBlock_stop
    (Omega : ActiveGaugeRegion d N)
    (source target : ActiveGaugeRegion.Site Omega) :
    (CMP99SourceActiveRegionChain.stop (M := M) Omega).SameTerminalBlock
      source target ↔ source = target := by
  rfl

theorem CMP99SourceActiveRegionChain.sameTerminalBlock_step
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (source target : ActiveGaugeRegion.Site Omega) :
    (CMP99SourceActiveRegionChain.step Omega hOmega tail).SameTerminalBlock
        source target ↔
      tail.SameTerminalBlock
        (cmp99ActiveCoarseSiteOfFine Omega hOmega source)
        (cmp99ActiveCoarseSiteOfFine Omega hOmega target) := by
  rfl

/-- `SameTerminalBlock` is invariant under the dependent cast forced by an
equality of two active-region objects on the same lattice. -/
theorem CMP99SourceActiveRegionChain.sameTerminalBlock_cast
    {N depth : ℕ} {Omega₁ Omega₂ : ActiveGaugeRegion d N}
    (h : Omega₁ = Omega₂)
    (regions : CMP99SourceActiveRegionChain d M N Omega₁ depth)
    (source target : ActiveGaugeRegion.Site Omega₁) :
    (h ▸ regions).SameTerminalBlock (h ▸ source) (h ▸ target) ↔
      regions.SameTerminalBlock source target := by
  subst h
  rfl

/-- Casting an active site along equality of region objects leaves its
underlying lattice site unchanged. -/
theorem activeGaugeRegionSite_cast_val
    {N : ℕ} {Omega₁ Omega₂ : ActiveGaugeRegion d N}
    (h : Omega₁ = Omega₂) (x : ActiveGaugeRegion.Site Omega₁) :
    (h ▸ x).1 = x.1 := by
  subst h
  rfl

/-- Round-trip transport in an arbitrary dependent family. -/
theorem dependent_cast_symm_cancel
    {α : Sort*} {a b : α} (h : a = b)
    {P : α → Sort*} (x : P b) :
    h ▸ (h.symm ▸ x) = x := by
  subst h
  rfl

/-- A one-step transported average of a coordinate probe is exactly the
coordinate probe at its owner block, with the literal transported value. -/
theorem cmp99SourceTransportedBlockAverageCLM_single
    {N' : ℕ} [NeZero N']
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (source : ActiveGaugeRegion.Site Omega) (v : g) :
    cmp99SourceTransportedBlockAverageCLM Omega transport
        (singleFinitePiLp source v) =
      singleFinitePiLp (cmp99ActiveCoarseSiteOfFine Omega hOmega source)
        (cmp99SourceBlockAverageWeight M d •
          transport (blockSite M N' source.1) source.1 v) := by
  apply PiLp.ext
  intro target
  rw [cmp99SourceTransportedBlockAverageCLM,
    cmp99TransportedBlockAverageCLM_apply]
  by_cases howner : target = cmp99ActiveCoarseSiteOfFine Omega hOmega source
  · subst target
    rw [singleFinitePiLp_self]
    let xs : {x : FinBox d (M * N') //
        x ∈ blockOf M N' (blockSite M N' source.1)} :=
      ⟨source.1, (mem_blockOf M N' (blockSite M N' source.1) source.1).2 rfl⟩
    have hxs : cmp99ActiveFineSiteOfBlock Omega
        (cmp99ActiveCoarseSiteOfFine Omega hOmega source) xs = source := by
      apply Subtype.ext
      rfl
    apply congrArg (fun z : g => cmp99SourceBlockAverageWeight M d • z)
    calc
      (∑ x, transport
          (cmp99ActiveCoarseSiteOfFine Omega hOmega source).1 x.1
          (singleFinitePiLp source v
            (cmp99ActiveFineSiteOfBlock Omega
              (cmp99ActiveCoarseSiteOfFine Omega hOmega source) x))) =
          transport (cmp99ActiveCoarseSiteOfFine Omega hOmega source).1 xs.1
            (singleFinitePiLp source v
              (cmp99ActiveFineSiteOfBlock Omega
                (cmp99ActiveCoarseSiteOfFine Omega hOmega source) xs)) := by
        apply Fintype.sum_eq_single xs
        intro x hxne
        have hsiteNe : cmp99ActiveFineSiteOfBlock Omega
            (cmp99ActiveCoarseSiteOfFine Omega hOmega source) x ≠ source := by
          intro heq
          apply hxne
          apply Subtype.ext
          exact congrArg (fun z => z.1) heq
        rw [singleFinitePiLp_of_ne v hsiteNe]
        exact map_zero _
      _ = transport (blockSite M N' source.1) source.1 v := by
        rw [hxs, singleFinitePiLp_self]
        rfl
  · rw [singleFinitePiLp_of_ne _ howner]
    simp only [smul_eq_zero]
    right
    apply Finset.sum_eq_zero
    intro x _hx
    have hxne : cmp99ActiveFineSiteOfBlock Omega target x ≠ source := by
      intro heq
      apply howner
      apply Subtype.ext
      change target.1 = blockSite M N' source.1
      have hxblock : blockSite M N' x.1 = target.1 :=
        (mem_blockOf M N' target.1 x.1).mp x.2
      rw [← hxblock]
      exact congrArg (fun z => blockSite M N' z.1) heq
    rw [singleFinitePiLp_of_ne v hxne]
    exact map_zero _

/-- The literal recursive generated mass `Q'^*Q'` has no matrix element
between different terminal blocks. -/
theorem CMP99SourceActiveRegionChain.generatedCountingMass_single_apply_eq_zero
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (source target : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc),
      ¬ regions.SameTerminalBlock source target →
      regions.generatedCountingMass hd hM rho spacing epsilon background
          chain fineSmall (singleFinitePiLp source v) target = 0 := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall source target v hnot
      change singleFinitePiLp source v target = 0
      apply singleFinitePiLp_of_ne
      exact fun h => hnot h.symm
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall source target v hnot
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      let transport := cmp99SourceWeightedPhysicalTransport rho background
      let Qhead := cmp99SourceTransportedBlockAverageCLM Omega transport
      let sourceCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega source
      let targetCoarse := cmp99ActiveCoarseSiteOfFine Omega hOmega target
      let sourceValue := cmp99SourceBlockAverageWeight M d •
        transport (blockSite M N' source.1) source.1 v
      have hnotTail : ¬ tail.SameTerminalBlock sourceCoarse targetCoarse := by
        exact hnot
      have htail := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
        sourceCoarse targetCoarse sourceValue hnotTail
      have haverage : Qhead (singleFinitePiLp source v) =
          singleFinitePiLp sourceCoarse sourceValue := by
        exact cmp99SourceTransportedBlockAverageCLM_single
          Omega hOmega transport source v
      change Qhead.adjoint
          ((tail.generatedCountingMass hd hM rho ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall)
              (Qhead (singleFinitePiLp source v))) target = 0
      rw [haverage]
      have hQadj : Qhead.adjoint =
          cmp99TransportedBlockSynthesisCLM Omega hOmega
            (cmp99SourceBlockAverageWeight M d) transport := by
        dsimp [Qhead]
        exact (cmp99TransportedBlockSynthesisCLM_eq_adjoint Omega hOmega
          (cmp99SourceBlockAverageWeight M d) transport).symm
      rw [hQadj]
      rw [cmp99TransportedBlockSynthesisCLM_apply]
      change cmp99SourceBlockAverageWeight M d •
          (transport (blockSite M N' target.1) target.1).symm
            ((tail.generatedCountingMass hd hM rho ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              Scale.toSourceScale.data.nextBackground chain.tail nextSmall)
                (singleFinitePiLp sourceCoarse sourceValue) targetCoarse) = 0
      rw [htail, map_zero, smul_zero]

/-- On the canonical lifted source chain, the recursive terminal-block
relation is literally equality of the coordinatewise order-`M^depth` owner. -/
theorem cmp99SourceIteratedLift_sameTerminalBlock_iff
    (Omega : ActiveGaugeRegion d N) :
    ∀ (depth : ℕ)
      (source target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth)),
      (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth).SameTerminalBlock
          source target ↔
        cmp99GeneratedTerminalBlockSite M N depth source.1 =
          cmp99GeneratedTerminalBlockSite M N depth target.1 := by
  intro depth
  induction depth with
  | zero =>
      intro source target
      simp only [cmp99SourceIteratedLiftActiveRegionChain.eq_def,
        CMP99SourceActiveRegionChain.sameTerminalBlock_stop]
      constructor
      · intro h
        simpa [cmp99GeneratedTerminalBlockSite] using
          congrArg (fun z => z.1) h
      · intro h
        apply Subtype.ext
        simpa [cmp99GeneratedTerminalBlockSite] using h
  | succ depth ih =>
      intro source target
      let fine := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
      let hFine : fine.BlockSaturated :=
        cmp99IteratedLiftActiveRegion_blockSaturated Omega depth
      have hregion : cmp99ActiveCoarseRegion (M := M)
          (N' := cmp99RegionalLatticeSize M N depth) fine =
          cmp99IteratedLiftActiveRegion (M := M) Omega depth := by
        simpa [fine] using cmp99ActiveCoarseRegion_iteratedLift_succ_eq
          (M := M) Omega depth
      let tailActual : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion (M := M)
            (N' := cmp99RegionalLatticeSize M N depth) fine) depth :=
        hregion.symm ▸
          cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
      let built := CMP99SourceActiveRegionChain.step fine hFine tailActual
      have hb : built =
          cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega
            (depth + 1) := by
        dsimp [built, cmp99SourceIteratedLiftActiveRegionChain, fine,
          tailActual, hFine]
        congr 1
        apply eq_of_heq
        exact eqRec_heq_iff_heq.mpr (cast_heq _ _).symm
      rw [← hb]
      dsimp [built]
      change tailActual.SameTerminalBlock
        (cmp99ActiveCoarseSiteOfFine fine hFine source)
        (cmp99ActiveCoarseSiteOfFine fine hFine target) ↔ _
      let sourceCoarseRaw := cmp99ActiveCoarseSiteOfFine fine hFine source
      let targetCoarseRaw := cmp99ActiveCoarseSiteOfFine fine hFine target
      let sourceCoarse : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega depth) :=
        hregion ▸ sourceCoarseRaw
      let targetCoarse : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega depth) :=
        hregion ▸ targetCoarseRaw
      have hrec := ih
        sourceCoarse targetCoarse
      have htailEq : hregion ▸ tailActual =
          cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth := by
        exact dependent_cast_symm_cancel
          (P := fun Omega' : ActiveGaugeRegion d
              (cmp99RegionalLatticeSize M N depth) =>
            CMP99SourceActiveRegionChain d M
              (cmp99RegionalLatticeSize M N depth) Omega' depth)
          hregion
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth)
      have hcast :=
        CMP99SourceActiveRegionChain.sameTerminalBlock_cast
          hregion tailActual sourceCoarseRaw targetCoarseRaw
      rw [htailEq] at hcast
      rw [← hcast, hrec]
      rw [cmp99GeneratedTerminalBlockSite_succ,
        cmp99GeneratedTerminalBlockSite_succ]
      have hsval : sourceCoarse.1 = blockSite M
          (cmp99RegionalLatticeSize M N depth) source.1 := by
        simpa [sourceCoarse, sourceCoarseRaw,
          cmp99ActiveCoarseSiteOfFine] using
          activeGaugeRegionSite_cast_val hregion sourceCoarseRaw
      have htval : targetCoarse.1 = blockSite M
          (cmp99RegionalLatticeSize M N depth) target.1 := by
        simpa [targetCoarse, targetCoarseRaw,
          cmp99ActiveCoarseSiteOfFine] using
          activeGaugeRegionSite_cast_val hregion targetCoarseRaw
      rw [hsval, htval]

set_option maxHeartbeats 400000 in
/-- A literal recursively generated counting mass is finite range as soon as
its intrinsic terminal-block relation has the stated metric diameter. -/
theorem CMP99SourceActiveRegionChain.generatedCountingMass_finiteRange
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (dist : ActiveGaugeRegion.Site Omega →
      ActiveGaugeRegion.Site Omega → ℕ) (R : ℕ)
    (hdiameter : ∀ source target,
      regions.SameTerminalBlock source target → dist target source ≤ R) :
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site Omega) (g := SUNLieCoord Nc)
      (regions.generatedCountingMass hd hM rho spacing epsilon background
        chain fineSmall)
      dist R := by
  letI : NeZero N := regions.neZero
  intro source target v hfar
  apply regions.generatedCountingMass_single_apply_eq_zero
    hd hM rho spacing epsilon background chain fineSmall source target v
  intro hsame
  exact (Nat.not_lt_of_ge (hdiameter source target hsame)) hfar

/-- On the canonical lifted geometry the literal generated counting mass has
the explicit, volume-independent terminal-block range `M^depth - 1`. -/
theorem cmp99SourceIteratedLift_generatedCountingMass_finiteRange
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (g := SUNLieCoord Nc)
      (regions.generatedCountingMass hd hM rho spacing epsilon background
        chain fineSmall)
      (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  apply regions.generatedCountingMass_finiteRange
    hd hM rho spacing epsilon background chain fineSmall
  intro source target hsame
  apply finBoxDist_le_of_same_generatedTerminalBlock (M := M) depth
  exact ((cmp99SourceIteratedLift_sameTerminalBlock_iff
    (M := M) Omega depth source target).1 hsame).symm

/-- The actual generated multiscale mass `Q'†Q'` inherits the same exact
terminal-block range from its proved equality with the recursive counting
mass. -/
theorem cmp99SourceIteratedLift_QprimeMass_finiteRange
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig d (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    let T := regions.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (g := SUNLieCoord Nc) (T.Qprime.adjoint.comp T.Qprime)
      (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega depth
  let T := regions.weightedQprimeTower hd hM rho spacing epsilon
    background chain fineSmall
  change FinitePiLpFiniteRange
    (ι := ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
    (g := SUNLieCoord Nc) (T.Qprime.adjoint.comp T.Qprime)
    (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1)
  rw [← regions.generatedCountingMass_eq_QprimeMass hd hM rho spacing epsilon
    background chain fineSmall]
  exact cmp99SourceIteratedLift_generatedCountingMass_finiteRange
    Omega depth hd hM rho spacing epsilon background chain fineSmall

end

end YangMills.RG
