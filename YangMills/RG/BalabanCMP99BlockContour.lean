/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ContourHolonomy

/-!
# Block-contained contours for the CMP99 average

This file replaces the arbitrary periodic-path witness on the pairs actually
used by a block average.  Starting at the canonical lower corner, it builds a
monotone positive-edge path to any site of the same block.  Every edge stays
inside the block and the length is at most `d * (M - 1)`.

The construction is one-scale.  It does not identify Balaban's recursive
multiscale contour convention or the averaged backgrounds entering `Q'_j`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' : ℕ} [NeZero d] [NeZero M] [NeZero N']
variable {G : Type*} [Group G]

/-- Embed an internal block coordinate at the canonical lower corner. -/
def cmp99BlockEmbed (y : FinBox d N') (r : FinBox d M) :
    FinBox d (M * N') :=
  fun i => ⟨M * (y i).val + (r i).val, by
    have hr := (r i).isLt
    have hy := (y i).isLt
    have hM : 0 < M := NeZero.pos M
    calc
      M * (y i).val + (r i).val < M * (y i).val + M := by omega
      _ = M * ((y i).val + 1) := by ring
      _ ≤ M * N' := Nat.mul_le_mul_left M hy⟩

@[simp] theorem cmp99BlockEmbed_mem_blockOf
    (y : FinBox d N') (r : FinBox d M) :
    cmp99BlockEmbed y r ∈ blockOf M N' y := by
  rw [mem_blockOf, blockSite_eq_iff_cube]
  intro i
  exact ⟨by simp [cmp99BlockEmbed], by
    simp only [cmp99BlockEmbed]
    have hr := (r i).isLt
    omega⟩

@[simp] theorem cmp99BlockEmbed_default (y : FinBox d N') :
    cmp99BlockEmbed y (default : FinBox d M) = blockBasepoint M N' y := by
  funext i
  apply Fin.ext
  change M * (y i).val + 0 = M * (y i).val
  omega

/-- Sum of the internal coordinate offsets. -/
def cmp99BlockOffsetWeight (r : FinBox d M) : ℕ :=
  ∑ i : Fin d, (r i).val

/-- Lower one strictly positive internal coordinate. -/
def cmp99BlockOffsetPred (r : FinBox d M) (i : Fin d)
    (hi : 0 < (r i).val) : FinBox d M :=
  Function.update r i ⟨(r i).val - 1, by
    have hr := (r i).isLt
    omega⟩

@[simp] theorem cmp99BlockOffsetPred_self
    (r : FinBox d M) (i : Fin d) (hi : 0 < (r i).val) :
    (cmp99BlockOffsetPred r i hi i).val = (r i).val - 1 := by
  simp [cmp99BlockOffsetPred]

theorem cmp99BlockOffsetPred_apply_of_ne
    (r : FinBox d M) (i j : Fin d) (hi : 0 < (r i).val) (hji : j ≠ i) :
    cmp99BlockOffsetPred r i hi j = r j := by
  simp [cmp99BlockOffsetPred, hji]

theorem cmp99BlockOffsetWeight_pred_lt
    (r : FinBox d M) (i : Fin d) (hi : 0 < (r i).val) :
    cmp99BlockOffsetWeight (cmp99BlockOffsetPred r i hi) <
      cmp99BlockOffsetWeight r := by
  apply Finset.sum_lt_sum
  · intro j _hj
    by_cases hji : j = i
    · subst j
      simp [cmp99BlockOffsetWeight, cmp99BlockOffsetPred, hi]
    · simp [cmp99BlockOffsetWeight,
        cmp99BlockOffsetPred_apply_of_ne r i j hi hji]
  · exact ⟨i, Finset.mem_univ _, by
      simp [cmp99BlockOffsetWeight, cmp99BlockOffsetPred, hi]⟩

/-- Lowering a positive internal coordinate and taking one positive fine
step recovers the original embedded site. -/
theorem shift_cmp99BlockEmbed_pred
    (y : FinBox d N') (r : FinBox d M) (i : Fin d)
    (hi : 0 < (r i).val) :
    (cmp99BlockEmbed y (cmp99BlockOffsetPred r i hi)).shift i =
      cmp99BlockEmbed y r := by
  funext j
  by_cases hji : j = i
  · subst j
    apply Fin.ext
    simp only [FinBox.shift, if_pos, cmp99BlockEmbed,
      cmp99BlockOffsetPred_self]
    rw [Nat.mod_eq_of_lt]
    · omega
    · have hr := (r i).isLt
      have hy := (y i).isLt
      have hM : 0 < M := NeZero.pos M
      calc
        M * (y i).val + ((r i).val - 1) + 1 =
            M * (y i).val + (r i).val := by omega
        _ < M * (y i).val + M := by omega
        _ = M * ((y i).val + 1) := by ring
        _ ≤ M * N' := Nat.mul_le_mul_left M hy
  · simp [FinBox.shift, hji, cmp99BlockEmbed,
      cmp99BlockOffsetPred_apply_of_ne r i j hi hji]

/-- Every edge of a literal path has both endpoints in `S`. -/
def OrientedLatticePath.StaysIn
    {a b : FinBox d (M * N')}
    (Gamma : OrientedLatticePath (G := G) a b)
    (S : Finset (FinBox d (M * N'))) : Prop :=
  ∀ e ∈ Gamma.edges,
    FiniteLatticeGeometry.src e ∈ S ∧ FiniteLatticeGeometry.dst e ∈ S

theorem OrientedLatticePath.StaysIn.trans
    {a b c : FinBox d (M * N')}
    {Gamma1 : OrientedLatticePath (G := G) a b}
    {Gamma2 : OrientedLatticePath (G := G) b c}
    {S : Finset (FinBox d (M * N'))}
    (h1 : Gamma1.StaysIn S) (h2 : Gamma2.StaysIn S) :
    (Gamma1.trans Gamma2).StaysIn S := by
  intro e he
  rw [OrientedLatticePath.trans, List.mem_append] at he
  exact he.elim (h1 e) (h2 e)

/-- Change only the certified endpoint of a path.  The literal edge list is
unchanged; exposing this operation makes dependent endpoint transports
transparent to the later support and length proofs. -/
def OrientedLatticePath.castEnd
    {a b c : FinBox d (M * N')}
    (h : b = c) (Gamma : OrientedLatticePath (G := G) a b) :
    OrientedLatticePath (G := G) a c :=
  h ▸ Gamma

@[simp] theorem OrientedLatticePath.castEnd_edges
    {a b c : FinBox d (M * N')}
    (h : b = c) (Gamma : OrientedLatticePath (G := G) a b) :
    (Gamma.castEnd h).edges = Gamma.edges := by
  subst c
  rfl

theorem OrientedLatticePath.StaysIn.castEnd
    {a b c : FinBox d (M * N')}
    {Gamma : OrientedLatticePath (G := G) a b}
    {S : Finset (FinBox d (M * N'))}
    (hStay : Gamma.StaysIn S) (h : b = c) :
    (Gamma.castEnd h).StaysIn S := by
  intro e he
  exact hStay e (by simpa using he)

theorem positiveCoordinatePath_blockEmbed_pred_staysIn
    (y : FinBox d N') (r : FinBox d M) (i : Fin d)
    (hi : 0 < (r i).val) :
    (positiveCoordinatePath (G := G)
      (cmp99BlockEmbed y (cmp99BlockOffsetPred r i hi)) i).StaysIn
        (blockOf M N' y) := by
  intro e he
  simp only [positiveCoordinatePath, List.mem_singleton] at he
  subst e
  constructor
  · change cmp99BlockEmbed y (cmp99BlockOffsetPred r i hi) ∈
      blockOf M N' y
    exact cmp99BlockEmbed_mem_blockOf y _
  · change (cmp99BlockEmbed y (cmp99BlockOffsetPred r i hi)).shift i ∈
      blockOf M N' y
    rw [shift_cmp99BlockEmbed_pred y r i hi]
    exact cmp99BlockEmbed_mem_blockOf y r

/-- A path from the lower corner to an internal coordinate, with its exact
geometric support and a Manhattan-length bound. -/
theorem exists_cmp99BlockEmbed_orientedPath
    (y : FinBox d N') (r : FinBox d M) :
    ∃ Gamma : OrientedLatticePath (G := G)
        (blockBasepoint M N' y) (cmp99BlockEmbed y r),
      Gamma.StaysIn (blockOf M N' y) ∧
      Gamma.edges.length ≤ cmp99BlockOffsetWeight r := by
  generalize hn : cmp99BlockOffsetWeight r = n
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
      by_cases hnzero : n = 0
      · have hsum : ∀ i : Fin d, (r i).val = 0 := by
          intro i
          have hle : (r i).val ≤ ∑ j : Fin d, (r j).val :=
            Finset.single_le_sum (s := Finset.univ)
              (f := fun j : Fin d => (r j).val)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          have htotal : (∑ j : Fin d, (r j).val) = 0 := by
            simpa [cmp99BlockOffsetWeight, hnzero] using hn
          omega
        have hr : r = (default : FinBox d M) := by
          funext i
          apply Fin.ext
          change (r i).val = 0
          exact hsum i
        subst r
        let Gamma : OrientedLatticePath (G := G)
            (blockBasepoint M N' y)
            (cmp99BlockEmbed y (default : FinBox d M)) :=
          (OrientedLatticePath.refl (G := G)
            (blockBasepoint M N' y)).castEnd
              (cmp99BlockEmbed_default y).symm
        refine ⟨Gamma, ?_, ?_⟩
        · intro e he
          simp [Gamma, OrientedLatticePath.refl] at he
        · simp [Gamma, OrientedLatticePath.refl, cmp99BlockOffsetWeight]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
        have hsumpos : 0 < ∑ i : Fin d, (r i).val := by
          have hweightpos : 0 < cmp99BlockOffsetWeight r := by
            rw [hn]
            exact hnpos
          exact hweightpos
        obtain ⟨i, _hiMem, hi⟩ :=
          (Finset.sum_pos_iff_of_nonneg
            (fun _ _ => Nat.zero_le _)).mp hsumpos
        let r' := cmp99BlockOffsetPred r i hi
        have hpred : cmp99BlockOffsetWeight r' < n := by
          rw [← hn]
          exact cmp99BlockOffsetWeight_pred_lt r i hi
        obtain ⟨Gamma, hStay, hLength⟩ :=
          ih (cmp99BlockOffsetWeight r') hpred r' rfl
        have hshift := shift_cmp99BlockEmbed_pred y r i hi
        let step : OrientedLatticePath (G := G)
            (cmp99BlockEmbed y r') (cmp99BlockEmbed y r) :=
          (positiveCoordinatePath (G := G) (cmp99BlockEmbed y r') i).castEnd
            (by simpa [r'] using hshift)
        refine ⟨Gamma.trans step, hStay.trans ?_, ?_⟩
        · exact (positiveCoordinatePath_blockEmbed_pred_staysIn
            (G := G) y r i hi).castEnd (by simpa [r'] using hshift)
        · calc
            (Gamma.trans step).edges.length = Gamma.edges.length + 1 := by
              simp [OrientedLatticePath.trans, step,
                positiveCoordinatePath]
            _ ≤ cmp99BlockOffsetWeight r' + 1 := Nat.add_le_add_right hLength 1
            _ ≤ cmp99BlockOffsetWeight r :=
              Nat.succ_le_of_lt (cmp99BlockOffsetWeight_pred_lt r i hi)
            _ = n := hn

/-- Internal coordinate of a fine site certified to lie in `y`'s block. -/
def cmp99BlockOffsetOfMem (y : FinBox d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) : FinBox d M :=
  fun i => ⟨(x i).val - M * (y i).val, by
    have hcube := (blockSite_eq_iff_cube M N' x y).mp
      ((mem_blockOf M N' y x).mp hx) i
    omega⟩

theorem cmp99BlockEmbed_offsetOfMem
    (y : FinBox d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) :
    cmp99BlockEmbed y (cmp99BlockOffsetOfMem y x hx) = x := by
  funext i
  apply Fin.ext
  simp only [cmp99BlockEmbed, cmp99BlockOffsetOfMem]
  have hcube := (blockSite_eq_iff_cube M N' x y).mp
    ((mem_blockOf M N' y x).mp hx) i
  omega

theorem cmp99BlockOffsetWeight_le
    (r : FinBox d M) :
    cmp99BlockOffsetWeight r ≤ d * (M - 1) := by
  calc
    cmp99BlockOffsetWeight r ≤ ∑ _i : Fin d, (M - 1) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Nat.le_sub_one_of_lt (r i).isLt
    _ = d * (M - 1) := by simp

/-- Source-facing one-scale block contour with containment and uniform length
certificates. -/
structure CMP99BlockContour (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) where
  path : OrientedLatticePath (G := G) (blockBasepoint M N' y) x.1
  staysInBlock : path.StaysIn (blockOf M N' y)
  length_le : path.edges.length ≤ d * (M - 1)

/-- Every fine site of a coarse block admits a certified block contour. -/
theorem nonempty_cmp99BlockContour (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) :
    Nonempty (CMP99BlockContour (G := G) y x) := by
  let r := cmp99BlockOffsetOfMem y x.1 x.2
  obtain ⟨Gamma0, hStay, hLength⟩ :=
    exists_cmp99BlockEmbed_orientedPath (G := G) y r
  have hend : cmp99BlockEmbed y r = x.1 :=
    cmp99BlockEmbed_offsetOfMem y x.1 x.2
  let Gamma : OrientedLatticePath (G := G) (blockBasepoint M N' y) x.1 :=
    Gamma0.castEnd hend
  refine ⟨⟨Gamma, ?_, ?_⟩⟩
  · exact hStay.castEnd hend
  · calc
      Gamma.edges.length ≤ cmp99BlockOffsetWeight r := by
        simpa [Gamma] using hLength
      _ ≤ d * (M - 1) := cmp99BlockOffsetWeight_le r

/-- A noncomputably selected certified contour for every fine site in a
coarse block. -/
noncomputable def concreteCMP99BlockContour (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) :
    CMP99BlockContour (G := G) y x :=
  Classical.choice (nonempty_cmp99BlockContour (G := G) y x)

/-- A total contour system whose restriction to every physical block is the
certified block-contained selection.  Outside the block (pairs never consumed
by the block average) it uses only the already proved periodic connectivity
witness. -/
noncomputable def cmp99BlockContainedContourSystem :
    CMP99ContourSystem d M N' G :=
  fun y x =>
    if hx : x ∈ blockOf M N' y then
      (concreteCMP99BlockContour (G := G) y ⟨x, hx⟩).path
    else
      concreteOrientedLatticePath (G := G) (blockBasepoint M N' y) x

@[simp] theorem cmp99BlockContainedContourSystem_of_mem
    (y : FinBox d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) :
    cmp99BlockContainedContourSystem (G := G) y x =
      (concreteCMP99BlockContour (G := G) y ⟨x, hx⟩).path := by
  simp [cmp99BlockContainedContourSystem, hx]

/-- Every contour actually used by a block average stays inside that block. -/
theorem cmp99BlockContainedContourSystem_staysIn
    (y : FinBox d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) :
    (cmp99BlockContainedContourSystem (G := G) y x).StaysIn
      (blockOf M N' y) := by
  rw [cmp99BlockContainedContourSystem_of_mem (G := G) y x hx]
  exact (concreteCMP99BlockContour (G := G) y ⟨x, hx⟩).staysInBlock

/-- Uniform one-scale length bound for every contour consumed by the average. -/
theorem cmp99BlockContainedContourSystem_length_le
    (y : FinBox d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) :
    (cmp99BlockContainedContourSystem (G := G) y x).edges.length ≤
      d * (M - 1) := by
  rw [cmp99BlockContainedContourSystem_of_mem (G := G) y x hx]
  exact (concreteCMP99BlockContour (G := G) y ⟨x, hx⟩).length_le

variable {Nc : ℕ} [NeZero Nc]

omit [NeZero Nc] in
/-- Endpoint gauge covariance specialized to the certified block-contained
selection. -/
theorem cmp99BlockContainedContourHolonomy_gaugeAct
    (u : GaugeTransform d (M * N') (SUN Nc))
    (A : GaugeConfig d (M * N') (SUN Nc))
    (y : FinBox d N') (x : FinBox d (M * N')) :
    cmp99ContourHolonomy
        (cmp99BlockContainedContourSystem (G := SUN Nc))
        (GaugeConfig.gaugeAct u A) y x =
      u (blockBasepoint M N' y) *
        cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc)) A y x *
        (u x)⁻¹ :=
  cmp99ContourHolonomy_gaugeAct
    (cmp99BlockContainedContourSystem (G := SUN Nc)) u A y x

/-- Gauge covariance of the full regional average with no contour-system
parameter left in its interface. -/
theorem cmp99AdjointBlockAverageCLM_blockContainedContour_gaugeAct
    (Omega : ActiveGaugeRegion d (M * N')) (w : ℝ)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (A : GaugeConfig d (M * N') (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99AdjointBlockAverageCLM Omega w rho
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc))
          (GaugeConfig.gaugeAct u A))
        (cmp99RegionalFineGaugeAct Omega rho u phi) =
      cmp99RegionalCoarseGaugeAct Omega rho u
        (cmp99AdjointBlockAverageCLM Omega w rho
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) A) phi) :=
  cmp99AdjointBlockAverageCLM_contour_gaugeAct Omega w rho
    (cmp99BlockContainedContourSystem (G := SUN Nc)) u A phi

end

end YangMills.RG
