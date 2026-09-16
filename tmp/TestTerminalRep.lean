import YangMills.RG.BalabanCMP99SourceEq395GlobalMiddleTransport
import YangMills.RG.BlockBasepointDistance

namespace YangMills.RG
open YangMills Matrix
noncomputable section

def cmp99GeneratedTerminalBlockBasepoint
    {d : ℕ} (M N depth : ℕ) [NeZero M] [NeZero N]
    (x : FinBox d N) : FinBox d (cmp99RegionalLatticeSize M N depth) :=
  fun i => ⟨M ^ depth * (x i).val, by
    rw [cmp99RegionalLatticeSize_eq_pow_mul]
    exact (Nat.mul_lt_mul_left (pow_pos (NeZero.pos M) depth)).2 (x i).isLt⟩

@[simp] theorem cmp99GeneratedTerminalBlockBasepoint_zero
    {d M N : ℕ} [NeZero M] [NeZero N] (x : FinBox d N) :
    cmp99GeneratedTerminalBlockBasepoint M N 0 x = x := by
  funext i
  apply Fin.ext
  simp [cmp99GeneratedTerminalBlockBasepoint]

theorem blockBasepoint_cmp99GeneratedTerminalBlockBasepoint
    {d M N : ℕ} [NeZero M] [NeZero N] (depth : ℕ) (x : FinBox d N) :
    blockBasepoint M (cmp99RegionalLatticeSize M N depth)
        (cmp99GeneratedTerminalBlockBasepoint M N depth x) =
      cmp99GeneratedTerminalBlockBasepoint M N (depth + 1) x := by
  funext i
  apply Fin.ext
  simp [blockBasepoint, cmp99GeneratedTerminalBlockBasepoint, pow_succ]
  ring

variable {d M N : ℕ} [NeZero d] [NeZero M] [NeZero N]

omit [NeZero d] [NeZero N] in
theorem terminalRepresentative_cast_val_test
    {N depth : ℕ} {Omega₁ Omega₂ : ActiveGaugeRegion d N}
    (h : Omega₁ = Omega₂)
    (regions : CMP99SourceActiveRegionChain d M N Omega₂ depth)
    (source : regions.terminalSite) :
    let castRegions := Eq.mpr (congrArg
      (fun region => CMP99SourceActiveRegionChain d M N region depth) h)
      regions
    let hsite := CMP99SourceActiveRegionChain.terminalSite_mpr h regions
    ((castRegions.terminalRepresentative (hsite.symm ▸ source)).1 : FinBox d N) =
      (regions.terminalRepresentative source).1 := by
  subst h
  rfl

omit [NeZero d] [NeZero N] in
theorem terminalRepresentative_congr_val_test
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    {regions₁ regions₂ : CMP99SourceActiveRegionChain d M N Omega depth}
    (h : regions₁ = regions₂) (source : regions₁.terminalSite) :
    let hsite := congrArg CMP99SourceActiveRegionChain.terminalSite h
    (regions₂.terminalRepresentative (hsite ▸ source)).1 =
      (regions₁.terminalRepresentative source).1 := by
  subst h
  rfl

omit [NeZero d] [NeZero N] in
theorem terminalRepresentative_congr_val_test'
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    {regions₁ regions₂ : CMP99SourceActiveRegionChain d M N Omega depth}
    (h : regions₁ = regions₂)
    (source₁ : regions₁.terminalSite) (source₂ : regions₂.terminalSite)
    (hsource :
      congrArg CMP99SourceActiveRegionChain.terminalSite h ▸ source₁ = source₂) :
    (regions₂.terminalRepresentative source₂).1 =
      (regions₁.terminalRepresentative source₁).1 := by
  subst h
  simp only [eq_mp_eq_cast] at hsource
  subst source₂
  rfl

universe u

theorem cast_cancel_any_test
    {A B : Sort u} (hAB : A = B) (hBA : B = A) (x : B) :
    hAB ▸ (hBA ▸ x) = x := by
  cases hAB
  rfl

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000 in
theorem terminalRepresentative_iterated_eq_basepoint
    (Omega : ActiveGaugeRegion d N) :
    ∀ (depth : ℕ),
      let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
      let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
        (M := M) Omega depth
      ∀ source : regions.terminalSite,
        (regions.terminalRepresentative source).1 =
          cmp99GeneratedTerminalBlockBasepoint M N depth
            ((hsite ▸ source).1) := by
  intro depth
  induction depth with
  | zero =>
      dsimp only
      intro source
      change source.1 = cmp99GeneratedTerminalBlockBasepoint M N 0 source.1
      rw [cmp99GeneratedTerminalBlockBasepoint_zero]
  | succ depth ih =>
      dsimp only
      intro source
      let fine := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
      have hFine : fine.BlockSaturated :=
        cmp99IteratedLiftActiveRegion_blockSaturated (M := M) Omega depth
      have hregion := cmp99ActiveCoarseRegion_iteratedLift_succ_eq
        (M := M) Omega depth
      let tailActual : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth) fine) depth :=
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
      let hbuiltSite := congrArg CMP99SourceActiveRegionChain.terminalSite hb
      let sourceBuilt : built.terminalSite := hbuiltSite.symm ▸ source
      have hsourceBuilt : hbuiltSite ▸ sourceBuilt = source := by
        exact cast_cancel_any_test hbuiltSite hbuiltSite.symm source
      have hbuiltRep :
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
            |>.terminalRepresentative source).1 =
          (built.terminalRepresentative sourceBuilt).1 := by
        exact terminalRepresentative_congr_val_test' hb sourceBuilt source
          hsourceBuilt
      change (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega
          (depth + 1) |>.terminalRepresentative source).1 = _
      rw [hbuiltRep]
      change blockBasepoint M (cmp99RegionalLatticeSize M N depth)
          (tailActual.terminalRepresentative sourceBuilt).1 = _
      let castTail := Eq.mpr (congrArg
        (fun region => CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth) region depth) hregion.symm)
        tailActual
      let hcastSite := CMP99SourceActiveRegionChain.terminalSite_mpr
        hregion.symm tailActual
      let sourceCast : castTail.terminalSite := hcastSite.symm ▸ sourceBuilt
      have hcastRep : (castTail.terminalRepresentative sourceCast).1 =
          (tailActual.terminalRepresentative sourceBuilt).1 := by
        exact terminalRepresentative_cast_val_test hregion.symm tailActual sourceBuilt
      have htailEq : castTail =
          cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth := by
        apply eq_of_heq
        have htailActual : HEq tailActual
            (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth) := by
          dsimp [tailActual]
          exact @eqRec_heq _
            (fun region : ActiveGaugeRegion d
                (cmp99RegionalLatticeSize M N depth) =>
              CMP99SourceActiveRegionChain d M
                (cmp99RegionalLatticeSize M N depth) region depth)
            _ _ hregion.symm
            (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth)
        exact HEq.trans (cast_heq _ tailActual) htailActual
      let htailSite := congrArg CMP99SourceActiveRegionChain.terminalSite htailEq
      let sourceCanonical :
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
            |>.terminalSite) := htailSite ▸ sourceCast
      have hcongrRep :
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
            |>.terminalRepresentative sourceCanonical).1 =
          (castTail.terminalRepresentative sourceCast).1 := by
        exact terminalRepresentative_congr_val_test htailEq sourceCast
      rw [← hcastRep, ← hcongrRep,
        ih sourceCanonical,
        blockBasepoint_cmp99GeneratedTerminalBlockBasepoint]
      congr 1
      apply congrArg Subtype.val
      apply eq_of_heq
      have hsourceCanonical : HEq sourceCanonical source := by
        exact HEq.trans (cast_heq _ sourceCast)
          (HEq.trans (cast_heq _ sourceBuilt) (cast_heq _ source))
      exact HEq.trans (cast_heq _ sourceCanonical)
        (HEq.trans hsourceCanonical (cast_heq _ source).symm)

end
end YangMills.RG
