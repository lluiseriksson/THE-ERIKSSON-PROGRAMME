import YangMills.RG.BalabanCMP89SourceNeumannCoarseDerivativeDecomposition
import YangMills.RG.BalabanCMP89SourceNeumannInternalBlockEnergy

/-!
# Restricted straight-path energy for the CMP89 Neumann derivative

The ambient straight-path identity sums over every starting point and hence
sees zero-extension boundary bonds.  The physical feedback estimate instead
sums only the straight paths attached to active coarse bonds.  At each path
layer, the map from an active coarse bond and a source-block point to the
corresponding fine positive bond is injective, and source geometry places its
image inside the literal Neumann internal-bond carrier.  Thus every layer is
bounded by the raw regional Neumann energy and the `M` layers cost exactly
`M`, with no active-volume or Dirichlet boundary term.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Starting data for all literal straight paths attached to active coarse
positive bonds. -/
abbrev CMP89SourceNeumannParallelStartIndex
    (Omega : ActiveGaugeRegion d (M * N')) :=
  Σ b : ActiveGaugeRegion.Bond
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
    {x : FinBox d (M * N') // x ∈ blockOf M N' b.1.1}

/-- The fine positive bond read at layer `k` of one active coarse straight
path. -/
def cmp89SourceNeumannParallelFineBondAt
    (Omega : ActiveGaugeRegion d (M * N')) (k : ℕ)
    (i : CMP89SourceNeumannParallelStartIndex Omega) :
    PositiveBond d (M * N') :=
  (((fun z => FinBox.shift z i.1.1.2)^[k] i.2.1), i.1.1.2)

/-- At a fixed layer, distinct coarse-bond/start pairs read distinct fine
positive bonds.  The owner block recovers the coarse source after the shift
is inverted. -/
theorem cmp89SourceNeumannParallelFineBondAt_injective
    (Omega : ActiveGaugeRegion d (M * N')) (k : ℕ) :
    Function.Injective (cmp89SourceNeumannParallelFineBondAt Omega k) := by
  intro i j hij
  rcases i with ⟨⟨⟨y, mu⟩, hb⟩, x⟩
  rcases j with ⟨⟨⟨y', mu'⟩, hb'⟩, x'⟩
  have hmu : mu = mu' := congrArg Prod.snd hij
  have hshift :
      (fun z => FinBox.shift z mu)^[k] x.1 =
        (fun z => FinBox.shift z mu')^[k] x'.1 :=
    congrArg Prod.fst hij
  subst mu'
  have hx : x.1 = x'.1 :=
    (iterShift_bijective (M * N') mu k).injective hshift
  have hy : y = y' := by
    calc
      y = blockSite M N' x.1 :=
        ((mem_blockOf M N' y x.1).mp x.2).symm
      _ = blockSite M N' x'.1 := by rw [hx]
      _ = y' := (mem_blockOf M N' y' x'.1).mp x'.2
  subst y'
  have hxx : x = x' := Subtype.ext hx
  subst x'
  rfl

/-- Every fine bond in the active straight-path index lies in the literal
Neumann internal-bond carrier. -/
theorem cmp89SourceNeumannParallelFineBondAt_mem_bonds
    (Omega : ActiveGaugeRegion d (M * N'))
    (i : CMP89SourceNeumannParallelStartIndex Omega)
    {k : ℕ} (hk : k < M) :
    cmp89SourceNeumannParallelFineBondAt Omega k i ∈ Omega.bonds := by
  rcases i with ⟨⟨⟨y, mu⟩, hb⟩, x⟩
  have hbEnds := (Finset.mem_filter.mp hb).2
  have hyBlock : blockOf M N' y ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff Omega y).mp hbEnds.1
  have hyShiftBlock : blockOf M N' (y.shift mu) ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff Omega (y.shift mu)).mp hbEnds.2
  have hsourceBlock :=
    blockSite_iterate_shift_eq_self_or_shift y x.1 mu x.2 k
      (Nat.le_of_lt hk)
  have htargetBlock :=
    blockSite_iterate_shift_eq_self_or_shift y x.1 mu x.2 (k + 1)
      (Nat.succ_le_of_lt hk)
  have hsucc :
      (((fun z => FinBox.shift z mu)^[k] x.1).shift mu) =
        (fun z => FinBox.shift z mu)^[k + 1] x.1 := by
    rw [Function.iterate_succ_apply']
  unfold cmp89SourceNeumannParallelFineBondAt
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  constructor
  · rcases hsourceBlock with hsourceBlock | hsourceBlock
    · exact hyBlock ((mem_blockOf M N' y _).mpr hsourceBlock)
    · exact hyShiftBlock
        ((mem_blockOf M N' (y.shift mu) _).mpr hsourceBlock)
  · rw [hsucc]
    rcases htargetBlock with htargetBlock | htargetBlock
    · exact hyBlock ((mem_blockOf M N' y _).mpr htargetBlock)
    · exact hyShiftBlock
        ((mem_blockOf M N' (y.shift mu) _).mpr htargetBlock)

/-- An injectively indexed family of internal straight paths costs at most
its length times the full raw Neumann internal-bond energy. -/
theorem sum_covariantPathEnergy_cmp99StraightPositivePath_le_neumannRaw
    {I : Type*} [Fintype I]
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (start : I → FinBox d (M * N')) (direction : I → Fin d)
    (n : ℕ)
    (hinjective : ∀ k < n, Function.Injective fun i : I =>
      (((fun z => FinBox.shift z (direction i))^[k] (start i)), direction i))
    (hinternal : ∀ i k, k < n →
      (((fun z => FinBox.shift z (direction i))^[k] (start i)), direction i) ∈
        Omega.bonds) :
    (∑ i : I,
      covariantPathEnergy rho U (extendZeroZeroCLM Omega phi)
        (cmp99StraightPositivePath (G := SUN Nc)
          (start i) (direction i) n).edges) ≤
      (n : ℝ) * ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 := by
  induction n with
  | zero =>
      simp [cmp99StraightPositivePath, covariantPathEnergy,
        OrientedLatticePath.refl]
  | succ n ih =>
      have hprevious := ih
        (fun k hk => hinjective k (Nat.lt.step hk))
        (fun i k hk => hinternal i k (Nat.lt.step hk))
      have hlayer :
          (∑ i : I,
            ‖covariantD0CLM rho U (extendZeroZeroCLM Omega phi)
              (((fun z => FinBox.shift z (direction i))^[n] (start i)),
                direction i)‖ ^ 2) ≤
            ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 := by
        let f : I → ActiveGaugeRegion.Bond Omega := fun i =>
          ⟨(((fun z => FinBox.shift z (direction i))^[n] (start i)), direction i),
            hinternal i n (Nat.lt_succ_self n)⟩
        have hf : Function.Injective f := by
          intro i j hij
          apply hinjective n (Nat.lt_succ_self n)
          exact congrArg Subtype.val hij
        rw [PiLp.norm_sq_eq_of_L2]
        calc
          (∑ i : I,
              ‖covariantD0CLM rho U (extendZeroZeroCLM Omega phi)
                (((fun z => FinBox.shift z (direction i))^[n] (start i)),
                  direction i)‖ ^ 2) =
            ∑ b ∈ Finset.univ.image f,
              ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2 := by
                rw [Finset.sum_image hf.injOn]
                rfl
          _ ≤ ∑ b : ActiveGaugeRegion.Bond Omega,
              ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2 := by
                exact Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
                  (fun _ _ _ => sq_nonneg _)
      simp_rw [covariantPathEnergy_cmp99StraightPositivePath_succ]
      rw [Finset.sum_add_distrib]
      calc
        (∑ i : I,
            covariantPathEnergy rho U (extendZeroZeroCLM Omega phi)
              (cmp99StraightPositivePath (G := SUN Nc)
                (start i) (direction i) n).edges) +
            ∑ i : I,
              ‖covariantD0CLM rho U (extendZeroZeroCLM Omega phi)
                (((fun z => FinBox.shift z (direction i))^[n] (start i)),
                  direction i)‖ ^ 2 ≤
          (n : ℝ) * ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 +
            ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 :=
              add_le_add hprevious hlayer
        _ = ((n + 1 : ℕ) : ℝ) *
            ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 := by
              push_cast
              ring

/-- The full family of active coarse straight paths pays exactly the physical
path length `M` against the raw regional Neumann energy. -/
theorem sum_cmp89SourceNeumannParallelPathEnergy_le_raw
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    (∑ i : CMP89SourceNeumannParallelStartIndex Omega,
      covariantPathEnergy rho U (extendZeroZeroCLM Omega phi)
        (cmp99SourceParallelTransportPath (G := SUN Nc)
          i.2.1 i.1.1.2).edges) ≤
      (M : ℝ) * ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 := by
  apply sum_covariantPathEnergy_cmp99StraightPositivePath_le_neumannRaw
    (Omega := Omega) (rho := rho) (U := U) (phi := phi)
    (start := fun i : CMP89SourceNeumannParallelStartIndex Omega => i.2.1)
    (direction := fun i => i.1.1.2) (n := M)
  · intro k hk
    exact cmp89SourceNeumannParallelFineBondAt_injective Omega k
  · intro i k hk
    exact cmp89SourceNeumannParallelFineBondAt_mem_bonds Omega i hk

end

end YangMills.RG
