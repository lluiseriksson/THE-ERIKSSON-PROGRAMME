import tmp.P4aPhysicalBase

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only finite telescoping layer for CMP85 (2.43).

The generic lemma is purely additive.  The physical increment is fixed
separately from the source-complete (2.42) producer, so the later dependent
`Fin` reindexing cannot alter its coefficient or operator order.  This file
is not compiler evidence and is not imported by the tracked tree.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Telescoping from source index one. -/
theorem scratch_sum_Ico_one_of_succ_eq_add
    {A : Type*} [AddCommMonoid A]
    (G correction : ℕ → A)
    (hstep : ∀ j, G (j + 1) = G j + correction j)
    (k : ℕ) :
    G (k + 1) = G 1 + ∑ j ∈ Finset.Ico 1 (k + 1), correction j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [hstep (k + 1), ih]
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
      ac_rfl

/-- Interval-local form of the same telescope.  Only the source steps that
actually enter the finite sum are required; no recurrence outside the
physical prefix range is manufactured. -/
theorem scratch_sum_Ico_one_of_succ_eq_add_on
    {A : Type*} [AddCommMonoid A]
    (G correction : ℕ → A)
    (k : ℕ)
    (hstep : ∀ j ∈ Finset.Ico 1 (k + 1),
      G (j + 1) = G j + correction j) :
    G (k + 1) = G 1 + ∑ j ∈ Finset.Ico 1 (k + 1), correction j := by
  revert hstep
  induction k with
  | zero =>
      intro hstep
      simp
  | succ k ih =>
      intro hstep
      have hlast : G (k + 1 + 1) = G (k + 1) + correction (k + 1) :=
        hstep (k + 1) (by
          simp only [Finset.mem_Ico]
          omega)
      have hprefix : ∀ j ∈ Finset.Ico 1 (k + 1),
          G (j + 1) = G j + correction j := by
        intro j hj
        exact hstep j (by
          simp only [Finset.mem_Ico] at hj ⊢
          omega)
      rw [hlast, ih hprefix]
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
      ac_rfl

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Literal source summand in CMP85 (2.42)/(2.43). -/
noncomputable def scratch_cmp85SourceGeneratedGreenIncrement
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (k : ScratchCMP85PositiveCoarseStep depth) :=
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  let Q := (T.towerAt r.1).Qprime
  let Qdag := (T.towerAt r.1).weightedAdjoint
  let G := scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall r
  let C := scratch_cmp85SourceGeneratedCoarseCovariance hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall k
  (scratch_cmp85SourcePrefixA (M := M) a r) ^ 2 *
      (T.towerAt r.1).terminalSpacing⁻¹ ^ 4 •
    G.comp (Qdag.comp (C.comp (Q.comp G)))

/-- Each positive source step is exactly addition of the literal increment;
this is only a named orientation of the already derived (2.42). -/
theorem scratch_cmp85SourceGeneratedPrefixGreen_succ_eq_add_increment
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (k : ScratchCMP85PositiveCoarseStep depth) :
    scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
        mass background0 chain fineSmall hsmall k.nextPrefix =
      scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
          mass background0 chain fineSmall hsmall k.currentPrefix +
        scratch_cmp85SourceGeneratedGreenIncrement hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall k := by
  exact scratch_cmp85SourceGeneratedGreenRecurrence_eq242 hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall k

/-! ## Proof-carrying natural-index adapter -/

/-- Turn a source integer `1 ≤ j ≤ depth` into the corresponding positive
prefix.  Both bounds remain explicit at this dictionary boundary. -/
def scratch_cmp85PositivePrefixOfNat
    {depth : ℕ} (j : ℕ) (hpos : 0 < j) (hle : j ≤ depth) :
    ScratchCMP85PositivePrefix depth :=
  ⟨⟨j, Nat.lt_succ_iff.mpr hle⟩, hpos⟩

/-- Turn a source integer `1 ≤ j < depth` into the corresponding positive
coarse step. -/
def scratch_cmp85PositiveCoarseStepOfNat
    {depth : ℕ} (j : ℕ) (hpos : 0 < j) (hlt : j < depth) :
    ScratchCMP85PositiveCoarseStep depth :=
  ⟨⟨j, hlt⟩, hpos⟩

/-- Total natural-index view of the internally generated Green family.  The
zero branch is only an adapter outside the source interval and is never used
as a physical recurrence premise. -/
noncomputable def scratch_cmp85SourceGeneratedPrefixGreenAtNat
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (j : ℕ) :=
  if hj : 0 < j ∧ j ≤ depth then
    scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
      mass background0 chain fineSmall hsmall
      (scratch_cmp85PositivePrefixOfNat j hj.1 hj.2)
  else 0

/-- Total natural-index view of the literal source increment. -/
noncomputable def scratch_cmp85SourceGeneratedGreenIncrementAtNat
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (j : ℕ) :=
  if hj : 0 < j ∧ j < depth then
    scratch_cmp85SourceGeneratedGreenIncrement hd hM Omega0 depth hspacing ha
      mass background0 chain fineSmall hsmall
      (scratch_cmp85PositiveCoarseStepOfNat j hj.1 hj.2)
  else 0

theorem scratch_cmp85SourceGeneratedPrefixGreenAtNat_succ_eq_add
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (j : ℕ) (hpos : 0 < j) (hlt : j < depth) :
    scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth hspacing ha
        mass background0 chain fineSmall hsmall (j + 1) =
      scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall j +
        scratch_cmp85SourceGeneratedGreenIncrementAtNat hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall j := by
  have hjle : j ≤ depth := Nat.le_of_lt hlt
  have hsuccpos : 0 < j + 1 := by omega
  have hsuccle : j + 1 ≤ depth := by omega
  simp only [scratch_cmp85SourceGeneratedPrefixGreenAtNat,
    scratch_cmp85SourceGeneratedGreenIncrementAtNat,
    dif_pos ⟨hsuccpos, hsuccle⟩, dif_pos ⟨hpos, hjle⟩,
    dif_pos ⟨hpos, hlt⟩]
  simpa only [scratch_cmp85PositivePrefixOfNat,
    scratch_cmp85PositiveCoarseStepOfNat,
    ScratchCMP85PositiveCoarseStep.currentPrefix,
    ScratchCMP85PositiveCoarseStep.nextPrefix, Fin.coe_castSucc,
    Fin.succ_val] using
      scratch_cmp85SourceGeneratedPrefixGreen_succ_eq_add_increment hd hM
        Omega0 depth hspacing ha mass background0 chain fineSmall hsmall
        (scratch_cmp85PositiveCoarseStepOfNat j hpos hlt)

/-- Finite source telescope with the independently generated base covariance
substituted.  The remaining natural-index adapter is supported exactly on
`1 ≤ j < depth`; the later public endpoint only reindexes that finite set. -/
theorem scratch_cmp85SourceGeneratedPrefixGreenAtDepth_eq_base_add_sum
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth hspacing ha
        mass background0 chain fineSmall hsmall depth =
      scratch_cmp85SourceGeneratedBaseCovariance hd hM Omega0 depth hdepth
          hspacing ha mass background0 chain fineSmall hsmall +
        ∑ j ∈ Finset.Ico 1 depth,
          scratch_cmp85SourceGeneratedGreenIncrementAtNat hd hM Omega0 depth
            hspacing ha mass background0 chain fineSmall hsmall j := by
  have hdepthEq : depth - 1 + 1 = depth := by omega
  have hstep : ∀ j ∈ Finset.Ico 1 (depth - 1 + 1),
      scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall (j + 1) =
        scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth
            hspacing ha mass background0 chain fineSmall hsmall j +
          scratch_cmp85SourceGeneratedGreenIncrementAtNat hd hM Omega0 depth
            hspacing ha mass background0 chain fineSmall hsmall j := by
    intro j hj
    simp only [Finset.mem_Ico, hdepthEq] at hj
    exact scratch_cmp85SourceGeneratedPrefixGreenAtNat_succ_eq_add hd hM
      Omega0 depth hspacing ha mass background0 chain fineSmall hsmall j
      (by omega) (by omega)
  have htelescope := scratch_sum_Ico_one_of_succ_eq_add_on
    (scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall)
    (scratch_cmp85SourceGeneratedGreenIncrementAtNat hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall)
    (depth - 1) hstep
  have hbase :
      scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall 1 =
        scratch_cmp85SourceGeneratedBaseCovariance hd hM Omega0 depth hdepth
          hspacing ha mass background0 chain fineSmall hsmall := by
    rw [scratch_cmp85SourceGeneratedPrefixGreenAtNat]
    simp only [dif_pos (by omega : 0 < (1 : ℕ) ∧ 1 ≤ depth)]
    simpa only [scratch_cmp85PositivePrefixOfNat,
      scratch_cmp85FirstPositivePrefix, scratch_cmp85FirstStep] using
      scratch_cmp85SourceGeneratedPrefixGreen_one_eq_baseCovariance hd hM
        Omega0 depth hdepth hspacing ha mass background0 chain fineSmall hsmall
  rw [hdepthEq] at htelescope
  rw [hbase] at htelescope
  exact htelescope

/-- The printed interval `1 ≤ j < depth` is exactly the proof-carrying
positive coarse-step index used by P3. -/
def scratch_cmp85PositiveCoarseStepEquivIco (depth : ℕ) :
    ScratchCMP85PositiveCoarseStep depth ≃
      {j : ℕ // j ∈ Finset.Ico 1 depth} where
  toFun k := ⟨k.1.val, Finset.mem_Ico.mpr ⟨k.2, k.1.isLt⟩⟩
  invFun j := ⟨⟨j.1, (Finset.mem_Ico.mp j.2).2⟩,
    (Finset.mem_Ico.mp j.2).1⟩
  left_inv k := by rfl
  right_inv j := by rfl

/-- Reindex the supported natural sum to the exact proof-carrying physical
step type.  No duplicate or out-of-range source scale survives. -/
theorem scratch_cmp85SourceGeneratedGreenIncrementAtNat_sum_eq_step_sum
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    (∑ j ∈ Finset.Ico 1 depth,
        scratch_cmp85SourceGeneratedGreenIncrementAtNat hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall j) =
      ∑ k : ScratchCMP85PositiveCoarseStep depth,
        scratch_cmp85SourceGeneratedGreenIncrement hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall k := by
  classical
  let f := fun j : {j : ℕ // j ∈ Finset.Ico 1 depth} =>
    scratch_cmp85SourceGeneratedGreenIncrementAtNat hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall j.1
  calc
    (∑ j ∈ Finset.Ico 1 depth,
        scratch_cmp85SourceGeneratedGreenIncrementAtNat hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall j) =
        ∑ j : {j : ℕ // j ∈ Finset.Ico 1 depth}, f j := by
          exact Finset.sum_subtype (Finset.Ico 1 depth) (fun _ => Iff.rfl) _
    _ = ∑ k : ScratchCMP85PositiveCoarseStep depth,
        f (scratch_cmp85PositiveCoarseStepEquivIco depth k) := by
          exact (Equiv.sum_comp
            (scratch_cmp85PositiveCoarseStepEquivIco depth) f).symm
    _ = ∑ k : ScratchCMP85PositiveCoarseStep depth,
        scratch_cmp85SourceGeneratedGreenIncrement hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall k := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [f, scratch_cmp85PositiveCoarseStepEquivIco,
            scratch_cmp85SourceGeneratedGreenIncrementAtNat,
            dif_pos ⟨k.2, k.1.isLt⟩,
            scratch_cmp85PositiveCoarseStepOfNat]

/-- Final positive prefix at the fixed generated depth. -/
def scratch_cmp85LastPositivePrefix
    (depth : ℕ) (hdepth : 0 < depth) : ScratchCMP85PositivePrefix depth :=
  ⟨Fin.last depth, hdepth⟩

/-- Source-complete finite Green expansion CMP85 (2.43), on one named fine
carrier.  The base covariance is generated independently in P4a and every
summand is the literal P3 increment indexed without duplication. -/
theorem scratch_cmp85SourceGeneratedGreenScaleSum_eq243
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
        mass background0 chain fineSmall hsmall
        (scratch_cmp85LastPositivePrefix depth hdepth) =
      scratch_cmp85SourceGeneratedBaseCovariance hd hM Omega0 depth hdepth
          hspacing ha mass background0 chain fineSmall hsmall +
        ∑ k : ScratchCMP85PositiveCoarseStep depth,
          scratch_cmp85SourceGeneratedGreenIncrement hd hM Omega0 depth
            hspacing ha mass background0 chain fineSmall hsmall k := by
  have hsum :=
    scratch_cmp85SourceGeneratedPrefixGreenAtDepth_eq_base_add_sum hd hM
      Omega0 depth hdepth hspacing ha mass background0 chain fineSmall hsmall
  rw [scratch_cmp85SourceGeneratedGreenIncrementAtNat_sum_eq_step_sum hd hM
    Omega0 depth hspacing ha mass background0 chain fineSmall hsmall] at hsum
  have hfinal :
      scratch_cmp85SourceGeneratedPrefixGreenAtNat hd hM Omega0 depth
          hspacing ha mass background0 chain fineSmall hsmall depth =
        scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
          mass background0 chain fineSmall hsmall
          (scratch_cmp85LastPositivePrefix depth hdepth) := by
    rw [scratch_cmp85SourceGeneratedPrefixGreenAtNat]
    simp only [dif_pos ⟨hdepth, le_rfl⟩]
    rfl
  rw [hfinal] at hsum
  exact hsum

end

end YangMills.RG
