/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ContourFirstVariationSupport
import YangMills.RG.BalabanCMP98SourceFieldScale
import YangMills.RG.BalabanCMP96ConstraintPivot

/-!
# Literal CMP98 contours avoid nonmatching CMP109 pivots

The distinguished bond `b₀(c)` is the last fine bond in the straight
length-`M` corridor representing the coarse bond `c`.  It crosses from the
source block of `c` to its target block.  Consequently:

* a contour whose two endpoints remain in one coarse block cannot contain
  any distinguished crossing bond;
* a straight length-`M` corridor contains `b₀(c)` only when it is the
  corridor of `c`.

This file proves those statements from the literal path definitions and
combines them for the four-contour word entering CMP98.  The mild condition
`2 ≤ N'` excludes the one-cell periodic torus, where source and target
coarse blocks are definitionally the same cell.
-/

namespace YangMills.RG

open YangMills

noncomputable section

set_option maxHeartbeats 2000000

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A nontrivial periodic coordinate shift changes the coarse site. -/
theorem finBox_shift_ne_of_two_le
    (hN' : 2 ≤ N') (x : FinBox d N') (i : Fin d) :
    x.shift i ≠ x := by
  intro h
  have hi := congrFun h i
  simp only [FinBox.shift, if_pos rfl] at hi
  have hval : ((x i).val + 1) % N' = (x i).val := by
    exact congrArg Fin.val hi
  rcases Nat.lt_or_ge ((x i).val + 1) N' with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hval
    omega
  · have heq : (x i).val + 1 = N' := by omega
    rw [heq, Nat.mod_self] at hval
    omega

/-- The endpoint of the distinguished fine bond is the lower corner of the
target coarse block. -/
theorem shift_cmp96ConstraintPivotSource_eq_targetBasepoint
    (c : PhysicalBond d N') :
    (cmp96ConstraintPivotSource
        (d := d) (L := M) (N' := N') c).shift c.2 =
      blockBasepoint M N' (c.1.shift c.2) := by
  have hM : M - 1 + 1 = M := by
    have := NeZero.pos M
    omega
  rw [cmp96ConstraintPivotSource]
  rw [← Function.iterate_succ_apply'
    (fun y : FinBox d (M * N') => FinBox.shift y c.2)
    (M - 1) (blockBasepoint M N' c.1)]
  simpa only [Nat.succ_eq_add_one, hM] using
    (show
      ((fun y : FinBox d (M * N') => FinBox.shift y c.2)^[M])
          (blockBasepoint M N' c.1) =
        blockBasepoint M N' (c.1.shift c.2) by
      change cmp99SourceTranslatedSite (blockBasepoint M N' c.1) c.2 =
        blockBasepoint M N' (c.1.shift c.2)
      rw [← cmp99BlockEmbed_default c.1,
        cmp99SourceTranslatedSite_blockEmbed,
        cmp99BlockEmbed_default])

/-- Reversing an edge list preserves avoidance of a physical positive bond. -/
theorem reverseLatticePath_avoids_physicalBond
    {G : Type*} [Group G]
    (es : List (ConcreteEdge d (M * N'))) (p : PhysicalBond d (M * N'))
    (havoid : ∀ e ∈ es, physicalBondOfEdge e ≠ p) :
    ∀ e ∈ reverseLatticePath (d := d) (N := M * N') (G := G) es,
      physicalBondOfEdge e ≠ p := by
  intro e he
  simp only [reverseLatticePath, List.mem_reverse, List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  simpa using havoid f hf

/-- Every edge in the literal positive straight path is one of its indexed
fine-bond samples. -/
theorem mem_cmp99StraightPositivePath_edges_exists
    {G : Type*} [Group G]
    (x : FinBox d (M * N')) (mu : Fin d) (n : ℕ)
    (e : ConcreteEdge d (M * N'))
    (he : e ∈ (cmp99StraightPositivePath (G := G) x mu n).edges) :
    ∃ k < n,
      physicalBondOfEdge e =
        (((fun y => FinBox.shift y mu)^[k] x, mu) :
          PhysicalBond d (M * N')) := by
  induction n with
  | zero =>
      simp only [cmp99StraightPositivePath_zero_edges, List.not_mem_nil] at he
  | succ n ih =>
      simp only [cmp99StraightPositivePath,
        OrientedLatticePath.castEnd_edges, OrientedLatticePath.trans,
        List.mem_append] at he
      rcases he with he | he
      · obtain ⟨k, hk, hbond⟩ := ih he
        exact ⟨k, Nat.lt.step hk, hbond⟩
      · simp only [positiveCoordinatePath, List.mem_singleton] at he
        subst e
        exact ⟨n, Nat.lt_succ_self n, rfl⟩

/-- A path which stays inside one coarse block cannot contain a distinguished
crossing bond. -/
theorem OrientedLatticePath.StaysIn.avoids_constraintPivot
    {G : Type*} [Group G]
    {a z : FinBox d (M * N')}
    (Gamma : OrientedLatticePath (G := G) a z)
    (y : FinBox d N') (c : PhysicalBond d N')
    (hN' : 2 ≤ N')
    (hstay : Gamma.StaysIn (blockOf M N' y)) :
    ∀ e ∈ Gamma.edges,
      physicalBondOfEdge e ≠
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c := by
  intro e he hbond
  have hinside := hstay e he
  have hsrc :
      blockSite M N' (FiniteLatticeGeometry.src e) = y :=
    (mem_blockOf M N' y (FiniteLatticeGeometry.src e)).mp hinside.1
  have hdst :
      blockSite M N' (FiniteLatticeGeometry.dst e) = y :=
    (mem_blockOf M N' y (FiniteLatticeGeometry.dst e)).mp hinside.2
  have hesource :
      e.source =
        cmp96ConstraintPivotSource (d := d) (L := M) (N' := N') c := by
    simpa [physicalBondOfEdge, cmp96ConstraintPivotBond] using
      congrArg Prod.fst hbond
  have hedir : e.dir = c.2 := by
    simpa [physicalBondOfEdge, cmp96ConstraintPivotBond] using
      congrArg Prod.snd hbond
  have hpivot :
      blockSite M N'
          (cmp96ConstraintPivotSource
            (d := d) (L := M) (N' := N') c) = c.1 :=
    blockSite_cmp96ConstraintPivotSource (L := M) c
  have htarget :
      blockSite M N'
          ((cmp96ConstraintPivotSource
            (d := d) (L := M) (N' := N') c).shift c.2) =
        c.1.shift c.2 := by
    rw [shift_cmp96ConstraintPivotSource_eq_targetBasepoint,
      blockSite_blockBasepoint]
  cases e with
  | mk source dir sign =>
      simp only at hesource hedir
      subst source
      subst dir
      change blockSite M N'
          (if sign then
            cmp96ConstraintPivotSource
              (d := d) (L := M) (N' := N') c
          else
            (cmp96ConstraintPivotSource
              (d := d) (L := M) (N' := N') c).shift c.2) = y at hsrc
      change blockSite M N'
          (if sign then
            (cmp96ConstraintPivotSource
              (d := d) (L := M) (N' := N') c).shift c.2
          else
            cmp96ConstraintPivotSource
              (d := d) (L := M) (N' := N') c) = y at hdst
      cases sign <;>
        simp only [Bool.false_eq_true, if_false, if_true] at hsrc hdst
      · have : c.1.shift c.2 = c.1 := by
          exact (htarget.symm.trans hsrc).trans
            (hpivot.symm.trans hdst).symm
        exact finBox_shift_ne_of_two_le hN' c.1 c.2 this
      · have : c.1.shift c.2 = c.1 := by
          exact (htarget.symm.trans hdst).trans
            (hpivot.symm.trans hsrc).symm
        exact finBox_shift_ne_of_two_le hN' c.1 c.2 this

/-- The source-block contour `Γ₁` avoids every distinguished crossing bond. -/
theorem cmp99SourceUbarGamma1_avoids_constraintPivot
    (b c : PhysicalBond d N') (x : FinBox d (M * N'))
    (hN' : 2 ≤ N') (hx : x ∈ blockOf M N' b.1) :
    ∀ e ∈ cmp99SourceUbarGamma1 (G := SUN Nc) b x,
      physicalBondOfEdge e ≠
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c := by
  exact OrientedLatticePath.StaysIn.avoids_constraintPivot
    (cmp99BlockContainedContourSystem (G := SUN Nc) b.1 x)
    b.1 c hN'
    (cmp99BlockContainedContourSystem_staysIn
      (G := SUN Nc) b.1 x hx)

/-- The return contour `Γ₃`, traversed inside the target block, also avoids
every distinguished crossing bond. -/
theorem cmp99SourceUbarGamma3_avoids_constraintPivot
    (b c : PhysicalBond d N') (x : FinBox d (M * N'))
    (hN' : 2 ≤ N') (hx : x ∈ blockOf M N' b.1) :
    ∀ e ∈ cmp99SourceUbarGamma3 (G := SUN Nc) b x,
      physicalBondOfEdge e ≠
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c := by
  let hx' := cmp99SourceTranslatedSite_mem_targetBlock b.1 b.2 x hx
  have hstay :=
    (concreteCMP99BlockContour (G := SUN Nc) (b.1.shift b.2)
      ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).staysInBlock
  have hforward :=
    OrientedLatticePath.StaysIn.avoids_constraintPivot
      (concreteCMP99BlockContour (G := SUN Nc) (b.1.shift b.2)
        ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).path
      (b.1.shift b.2) c hN' hstay
  simpa only [cmp99SourceUbarGamma3, dif_pos hx,
    OrientedLatticePath.symm] using
      reverseLatticePath_avoids_physicalBond
        (G := SUN Nc)
        (concreteCMP99BlockContour (G := SUN Nc) (b.1.shift b.2)
          ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).path.edges
        (cmp96ConstraintPivotBond
          (d := d) (L := M) (N' := N') c)
        hforward

/-- The translated middle corridor can hit `b₀(c)` only in the matching
coarse row. -/
theorem cmp99SourceUbarGamma2_avoids_constraintPivot_of_ne
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' b.1) :
    ∀ e ∈ cmp99SourceUbarGamma2 (G := SUN Nc) b x,
      physicalBondOfEdge e ≠
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c := by
  intro e he hbond
  have he' :
      e ∈ (cmp99StraightPositivePath
        (G := SUN Nc) x b.2 M).edges := by
    simpa [cmp99SourceUbarGamma2, cmp99SourceParallelTransportPath] using he
  obtain ⟨k, hk, hek⟩ :=
    mem_cmp99StraightPositivePath_edges_exists
      (G := SUN Nc) x b.2 M e he'
  have hsample :
      (((fun y => FinBox.shift y b.2)^[k] x, b.2) :
          PhysicalBond d (M * N')) =
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c :=
    hek.symm.trans hbond
  exact hbc
    ((cmp96ConstraintSample_eq_pivot_iff b c x hk
      ((mem_blockOf M N' b.1 x).mp hx)).mp hsample).1

/-- The straight basepoint corridor can hit `b₀(c)` only in the matching
coarse row. -/
theorem cmp98SourceCoarseBondPath_avoids_constraintPivot_of_ne
    (b c : PhysicalBond d N') (hbc : b ≠ c) :
    ∀ e ∈ cmp98SourceCoarseBondPath (Nc := Nc) (M := M) b,
      physicalBondOfEdge e ≠
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c := by
  intro e he hbond
  have he' :
      e ∈ (cmp99StraightPositivePath
        (G := SUN Nc) (blockBasepoint M N' b.1) b.2 M).edges := by
    simpa [cmp98SourceCoarseBondPath,
      cmp99SourceParallelTransportPath] using he
  obtain ⟨k, hk, hek⟩ :=
    mem_cmp99StraightPositivePath_edges_exists
      (G := SUN Nc) (blockBasepoint M N' b.1) b.2 M e he'
  have hsample :
      (((fun y => FinBox.shift y b.2)^[k]
          (blockBasepoint M N' b.1), b.2) :
          PhysicalBond d (M * N')) =
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c :=
    hek.symm.trans hbond
  exact hbc
    ((cmp96ConstraintSample_eq_pivot_iff b c
      (blockBasepoint M N' b.1) hk
      (blockSite_blockBasepoint M N' b.1)).mp hsample).1

/-- The complete four-contour word in a nonmatching coarse row avoids the
distinguished pivot bond exactly. -/
theorem cmp98SourceFourContourEdges_avoids_constraintPivot_of_ne
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (x : FinBox d (M * N')) (hN' : 2 ≤ N')
    (hx : x ∈ blockOf M N' b.1) :
    ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
      physicalBondOfEdge e ≠
        cmp96ConstraintPivotBond (d := d) (L := M) (N' := N') c := by
  intro e he
  by_cases h1 : e ∈ cmp99SourceUbarGamma1 (G := SUN Nc) b x
  · exact cmp99SourceUbarGamma1_avoids_constraintPivot
      b c x hN' hx e h1
  by_cases h2 : e ∈ cmp99SourceUbarGamma2 (G := SUN Nc) b x
  · exact cmp99SourceUbarGamma2_avoids_constraintPivot_of_ne
      b c hbc x hx e h2
  by_cases h3 : e ∈ cmp99SourceUbarGamma3 (G := SUN Nc) b x
  · exact cmp99SourceUbarGamma3_avoids_constraintPivot
      b c x hN' hx e h3
  have h4 :
      e ∈ reverseLatticePath (d := d) (N := M * N') (G := SUN Nc)
        (cmp98SourceCoarseBondPath (Nc := Nc) b) := by
    simpa [cmp98SourceFourContourEdges, h1, h2, h3] using he
  exact reverseLatticePath_avoids_physicalBond
    (G := SUN Nc)
    (cmp98SourceCoarseBondPath (Nc := Nc) (M := M) b)
    (cmp96ConstraintPivotBond
      (d := d) (L := M) (N' := N') c)
    (cmp98SourceCoarseBondPath_avoids_constraintPivot_of_ne
      (Nc := Nc) b c hbc) e h4

end

end YangMills.RG
