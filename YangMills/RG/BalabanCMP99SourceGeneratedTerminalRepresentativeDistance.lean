import YangMills.RG.BalabanCMP99SourceEq395GlobalMiddleTransport
import YangMills.RG.BlockBasepointDistance

/-!
# Literal representatives of the generated terminal lattice

The terminal site of the canonical CMP99 regional chain is definitionally
hidden behind dependent transports.  This module proves that the recursively
chosen fine representative is nevertheless the literal iterated lower block
corner `M ^ depth * x`.  This is the source-faithful metric bridge needed to
move the generated middle-kernel decay from terminal representatives back to
the physical coarse coordinates.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

/-- The literal lower corner of the depth-`depth` block owned by `x`. -/
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

/-- One more lower-corner choice is multiplication by one more factor `M`. -/
theorem blockBasepoint_cmp99GeneratedTerminalBlockBasepoint
    {d M N : ℕ} [NeZero M] [NeZero N] (depth : ℕ) (x : FinBox d N) :
    blockBasepoint M (cmp99RegionalLatticeSize M N depth)
        (cmp99GeneratedTerminalBlockBasepoint M N depth x) =
      cmp99GeneratedTerminalBlockBasepoint M N (depth + 1) x := by
  funext i
  apply Fin.ext
  simp [blockBasepoint, cmp99GeneratedTerminalBlockBasepoint, pow_succ]
  ring

/-- After the canonical equality of lattice sizes is exposed, the generated
terminal corner is literally the ordinary block basepoint of scale
`M ^ depth`. -/
theorem cmp99GeneratedTerminalBlockBasepoint_cast_eq_blockBasepoint
    {d M N : ℕ} [NeZero M] [NeZero N] (depth : ℕ) (x : FinBox d N) :
    let hsize := cmp99RegionalLatticeSize_eq_pow_mul M N depth
    hsize ▸ cmp99GeneratedTerminalBlockBasepoint M N depth x =
      blockBasepoint (M ^ depth) N x := by
  dsimp only
  funext i
  apply Fin.ext
  rw [finBox_cast_apply_val]
  rfl

/-- Generated lower corners multiply physical distance by the complete
iterated scale. -/
theorem finBoxDist_cmp99GeneratedTerminalBlockBasepoint_eq_mul
    {d M N : ℕ} [NeZero M] [NeZero N] (depth : ℕ) (x y : FinBox d N) :
    finBoxDist (cmp99GeneratedTerminalBlockBasepoint M N depth x)
        (cmp99GeneratedTerminalBlockBasepoint M N depth y) =
      M ^ depth * finBoxDist x y := by
  let hsize := cmp99RegionalLatticeSize_eq_pow_mul M N depth
  calc
    finBoxDist (cmp99GeneratedTerminalBlockBasepoint M N depth x)
        (cmp99GeneratedTerminalBlockBasepoint M N depth y) =
      finBoxDist
        (hsize ▸ cmp99GeneratedTerminalBlockBasepoint M N depth x)
        (hsize ▸ cmp99GeneratedTerminalBlockBasepoint M N depth y) := by
          symm
          exact finBoxDist_cast_size hsize _ _
    _ = finBoxDist (blockBasepoint (M ^ depth) N x)
        (blockBasepoint (M ^ depth) N y) := by
          rw [cmp99GeneratedTerminalBlockBasepoint_cast_eq_blockBasepoint,
            cmp99GeneratedTerminalBlockBasepoint_cast_eq_blockBasepoint]
    _ = M ^ depth * finBoxDist x y :=
      finBoxDist_blockBasepoint_eq_mul (M ^ depth) N x y

variable {d M N : ℕ} [NeZero d] [NeZero M] [NeZero N]

omit [NeZero d] [NeZero N] in
/-- Casting the starting active region does not alter the lattice coordinate
of the recursively chosen terminal representative. -/
theorem CMP99SourceActiveRegionChain.terminalRepresentative_cast_val
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
/-- Congruent typed chains choose the same terminal representative when their
dependent terminal arguments are transported coherently. -/
theorem CMP99SourceActiveRegionChain.terminalRepresentative_congr_val
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    {regions₁ regions₂ : CMP99SourceActiveRegionChain d M N Omega depth}
    (h : regions₁ = regions₂)
    (source₁ : regions₁.terminalSite) (source₂ : regions₂.terminalSite)
    (hsource :
      congrArg CMP99SourceActiveRegionChain.terminalSite h ▸ source₁ = source₂) :
    (regions₂.terminalRepresentative source₂).1 =
      (regions₁.terminalRepresentative source₁).1 := by
  subst h
  subst source₂
  rfl

universe u

/-- Round-trip casts cancel even when the two equality witnesses are not
definitionally the same proof. -/
theorem cast_cancel_of_opposite_equalities
    {A B : Sort u} (hAB : A = B) (hBA : B = A) (x : B) :
    hAB ▸ (hBA ▸ x) = x := by
  cases hAB
  rfl

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000 in
/-- The canonical recursively chosen terminal representative is exactly the
lower corner at scale `M ^ depth` of the original physical terminal site. -/
theorem cmp99SourceIteratedLift_terminalRepresentative_eq_basepoint
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
        exact cast_cancel_of_opposite_equalities hbuiltSite hbuiltSite.symm source
      have hbuiltRep :
          (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
            |>.terminalRepresentative source).1 =
          (built.terminalRepresentative sourceBuilt).1 := by
        exact CMP99SourceActiveRegionChain.terminalRepresentative_congr_val
          hb sourceBuilt source hsourceBuilt
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
        exact CMP99SourceActiveRegionChain.terminalRepresentative_cast_val
          hregion.symm tailActual sourceBuilt
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
        exact CMP99SourceActiveRegionChain.terminalRepresentative_congr_val
          htailEq sourceCast sourceCanonical rfl
      rw [← hcastRep, ← hcongrRep, ih sourceCanonical,
        blockBasepoint_cmp99GeneratedTerminalBlockBasepoint]
      congr 1
      apply congrArg Subtype.val
      apply eq_of_heq
      have hsourceCanonical : HEq sourceCanonical source := by
        exact HEq.trans (cast_heq _ sourceCast)
          (HEq.trans (cast_heq _ sourceBuilt) (cast_heq _ source))
      exact HEq.trans (cast_heq _ sourceCanonical)
        (HEq.trans hsourceCanonical (cast_heq _ source).symm)

/-- On the canonical generated chain, distance between terminal
representatives is exactly `M ^ depth` times the physical coarse distance. -/
theorem cmp99SourceIteratedLift_terminalRepresentative_finBoxDist
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
      (M := M) Omega depth
    ∀ source target : regions.terminalSite,
      finBoxDist (regions.terminalRepresentative target).1
          (regions.terminalRepresentative source).1 =
        M ^ depth * finBoxDist ((hsite ▸ target).1) ((hsite ▸ source).1) := by
  dsimp only
  intro source target
  rw [cmp99SourceIteratedLift_terminalRepresentative_eq_basepoint,
    cmp99SourceIteratedLift_terminalRepresentative_eq_basepoint]
  exact finBoxDist_cmp99GeneratedTerminalBlockBasepoint_eq_mul depth _ _

/-- The original physical coarse distance on the dependent terminal-site
type of the canonical generated chain. -/
def cmp99SourceIteratedLiftPhysicalTerminalDist
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :=
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega depth
  fun (target source : regions.terminalSite) =>
    finBoxDist ((hsite ▸ target).1) ((hsite ▸ source).1)

/-- The physical coarse terminal distance is bounded by the fine distance
between the canonical representatives. -/
theorem cmp99SourceIteratedLiftPhysicalTerminalDist_le_representative
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    ∀ target source : regions.terminalSite,
      cmp99SourceIteratedLiftPhysicalTerminalDist (M := M) Omega depth
          target source ≤
        finBoxDist (regions.terminalRepresentative target).1
          (regions.terminalRepresentative source).1 := by
  dsimp only
  intro target source
  rw [cmp99SourceIteratedLift_terminalRepresentative_finBoxDist]
  have hpow : 1 ≤ M ^ depth := one_le_pow₀ (NeZero.one_le : 1 ≤ M)
  simpa only [one_mul] using Nat.mul_le_mul_right
    (cmp99SourceIteratedLiftPhysicalTerminalDist (M := M) Omega depth
      target source) hpow

end

end YangMills.RG
