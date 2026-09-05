/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99BlockContour
import YangMills.RG.BalabanCMP116WilsonHessianLiteral

/-!
# Literal CMP99/CMP109 contours for the physical Ubar background

Bałaban's CMP109 equation (0.12) uses, for a positive coarse bond `c`
and `x` in the source block, the ordered product

`U(c₋,x) * U([x,x']) * U(x',c₊) * U(-c)`.

Here `[x,x']` is defined in the source as the parallel translate of `c`
to `x`.  This module constructs that convention literally on the periodic
box.  The first and third factors use the already certified block-contained
contours; the middle factor is the straight path of exactly `M` positive
fine bonds.  The coarse base field `U(c)` is the same straight transport
started at the source block basepoint, rather than an unrelated coarse
configuration supplied after the fact.

The construction is geometric.  Small-field estimates for these literal
paths are deliberately left to the analytic scale producer.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' : ℕ} [NeZero d] [NeZero M] [NeZero N']
variable {G : Type*} [Group G]

/-- The source-faithful translated site `x' = x + M e_mu`. -/
def cmp99SourceTranslatedSite (x : FinBox d (M * N')) (mu : Fin d) :
    FinBox d (M * N') :=
  (fun y => FinBox.shift y mu)^[M] x

/-- The straight positive path of `n` lattice bonds in direction `mu`. -/
def cmp99StraightPositivePath (x : FinBox d (M * N')) (mu : Fin d) :
    (n : ℕ) → OrientedLatticePath (G := G) x
      ((fun y => FinBox.shift y mu)^[n] x)
  | 0 => OrientedLatticePath.refl (G := G) x
  | n + 1 =>
      let previous : OrientedLatticePath (G := G) x
          ((fun y => FinBox.shift y mu)^[n] x) :=
        cmp99StraightPositivePath x mu n
      let next := positiveCoordinatePath (G := G)
        ((fun y => FinBox.shift y mu)^[n] x) mu
      (previous.trans next).castEnd (by
        rw [Function.iterate_succ_apply'])

@[simp] theorem cmp99StraightPositivePath_zero_edges
    (x : FinBox d (M * N')) (mu : Fin d) :
    (cmp99StraightPositivePath (G := G) x mu 0).edges = [] :=
  rfl

theorem cmp99StraightPositivePath_length
    (x : FinBox d (M * N')) (mu : Fin d) (n : ℕ) :
    (cmp99StraightPositivePath (G := G) x mu n).edges.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cmp99StraightPositivePath, OrientedLatticePath.castEnd_edges,
        OrientedLatticePath.trans, List.length_append,
        positiveCoordinatePath, List.length_singleton, ih]

/-- The middle contour `[x,x']` in CMP109 (0.12). -/
def cmp99SourceParallelTransportPath
    (x : FinBox d (M * N')) (mu : Fin d) :
    OrientedLatticePath (G := G) x (cmp99SourceTranslatedSite x mu) :=
  cmp99StraightPositivePath (G := G) x mu M

@[simp] theorem cmp99SourceParallelTransportPath_length
    (x : FinBox d (M * N')) (mu : Fin d) :
    (cmp99SourceParallelTransportPath (G := G) x mu).edges.length = M :=
  cmp99StraightPositivePath_length (G := G) x mu M

/-- Parallel translation commutes with the internal-coordinate block
embedding, including across the periodic seam. -/
theorem cmp99SourceTranslatedSite_blockEmbed
    (y : FinBox d N') (r : FinBox d M) (mu : Fin d) :
    cmp99SourceTranslatedSite (cmp99BlockEmbed y r) mu =
      cmp99BlockEmbed (y.shift mu) r := by
  funext i
  apply Fin.ext
  by_cases hi : i = mu
  · subst i
    rw [cmp99SourceTranslatedSite, iterShift_apply_self]
    simp only [cmp99BlockEmbed, FinBox.shift, if_pos]
    have hM : 0 < M := NeZero.pos M
    have hN : 0 < N' := NeZero.pos N'
    have hr : (r mu).val < M := (r mu).isLt
    have hy : (y mu).val < N' := (y mu).isLt
    by_cases hwrap : (y mu).val + 1 < N'
    · rw [Nat.mod_eq_of_lt hwrap]
      have hroom : (y mu).val + 2 ≤ N' := by omega
      have hfine : M * (y mu).val + (r mu).val + M < M * N' := by
        calc
          M * (y mu).val + (r mu).val + M =
              M * ((y mu).val + 1) + (r mu).val := by ring
          _ < M * ((y mu).val + 1) + M := Nat.add_lt_add_left hr _
          _ = M * ((y mu).val + 2) := by ring
          _ ≤ M * N' := Nat.mul_le_mul_left M hroom
      rw [Nat.mod_eq_of_lt hfine]
      ring
    · have hlast : (y mu).val + 1 = N' := by omega
      rw [hlast, Nat.mod_self]
      have hsplit : M * (y mu).val + (r mu).val + M =
          M * N' + (r mu).val := by
        calc
          M * (y mu).val + (r mu).val + M =
              M * ((y mu).val + 1) + (r mu).val := by ring
          _ = M * N' + (r mu).val := by rw [hlast]
      have hMN : M ≤ M * N' := by
        simpa using Nat.mul_le_mul_left M (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N'))
      have hrMN : (r mu).val < M * N' := lt_of_lt_of_le hr hMN
      rw [hsplit, Nat.add_mod, Nat.mod_self, zero_add,
        Nat.mod_eq_of_lt hrMN]
      simpa using Nat.mod_eq_of_lt hrMN
  · rw [cmp99SourceTranslatedSite, iterShift_apply_ne _ _ _ hi]
    simp [cmp99BlockEmbed, FinBox.shift, hi]

/-- Parallel translation by a coarse positive bond sends every point of its
source block into the corresponding point of its target block. -/
theorem cmp99SourceTranslatedSite_mem_targetBlock
    (y : FinBox d N') (mu : Fin d) (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) :
    cmp99SourceTranslatedSite x mu ∈ blockOf M N' (y.shift mu) := by
  let r := cmp99BlockOffsetOfMem y x hx
  have hxrepr : cmp99BlockEmbed y r = x :=
    cmp99BlockEmbed_offsetOfMem y x hx
  rw [← hxrepr, cmp99SourceTranslatedSite_blockEmbed]
  exact cmp99BlockEmbed_mem_blockOf (y.shift mu) r

/-- The literal first contour `c_- -> x`. -/
def cmp99SourceUbarGamma1 (b : PhysicalBond d N')
    (x : FinBox d (M * N')) :
    List (ConcreteEdge d (M * N')) :=
  (cmp99BlockContainedContourSystem (G := G) b.1 x).edges

/-- The literal parallel-transport contour `[x,x']`. -/
def cmp99SourceUbarGamma2 (b : PhysicalBond d N')
    (x : FinBox d (M * N')) :
    List (ConcreteEdge d (M * N')) :=
  (cmp99SourceParallelTransportPath (G := G) x b.2).edges

/-- The literal return contour `x' -> c_+`.  Outside the source block, where
the Ubar sum never evaluates it, a generic periodic path only makes the
function total. -/
def cmp99SourceUbarGamma3 (b : PhysicalBond d N')
    (x : FinBox d (M * N')) :
    List (ConcreteEdge d (M * N')) :=
  if hx : x ∈ blockOf M N' b.1 then
    let hx' := cmp99SourceTranslatedSite_mem_targetBlock b.1 b.2 x hx
    ((concreteCMP99BlockContour (G := G) (b.1.shift b.2)
      ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).path.symm).edges
  else
    (concreteOrientedLatticePath (G := G)
      (cmp99SourceTranslatedSite x b.2)
      (blockBasepoint M N' (b.1.shift b.2))).edges

/-- The coarse base background printed as `U(c)` in CMP109 (0.12): the fine
background transported along the positive coarse bond. -/
def cmp99SourceBaseCoarseBackground (A : GaugeConfig d (M * N') G) :
    GaugeConfig d N' G :=
  gaugeConfigOfPositiveBonds fun b =>
    (cmp99SourceParallelTransportPath (G := G)
      (blockBasepoint M N' b.1) b.2).holonomy A

@[simp] theorem cmp99SourceBaseCoarseBackground_apply_pos
    (A : GaugeConfig d (M * N') G) (b : PhysicalBond d N') :
    cmp99SourceBaseCoarseBackground A (positiveEdgeOfPhysicalBond b) =
      (cmp99SourceParallelTransportPath (G := G)
        (blockBasepoint M N' b.1) b.2).holonomy A := by
  simp [cmp99SourceBaseCoarseBackground, positiveEdgeOfPhysicalBond,
    gaugeConfigOfPositiveBonds]

/-! ## Certificates consumed by the physical scale package -/

theorem cmp99SourceUbarGamma1_path (b : PhysicalBond d N')
    (x : FinBox d (M * N')) (_hx : x ∈ blockOf M N' b.1) :
    IsPathFrom (G := G) (blockBasepoint M N' b.1)
      (cmp99SourceUbarGamma1 (G := G) b x) := by
  exact (cmp99BlockContainedContourSystem (G := G) b.1 x).isPath

theorem cmp99SourceUbarGamma1_end (b : PhysicalBond d N')
    (x : FinBox d (M * N')) (_hx : x ∈ blockOf M N' b.1) :
    pathEnd (G := G) (blockBasepoint M N' b.1)
      (cmp99SourceUbarGamma1 (G := G) b x) = x := by
  exact (cmp99BlockContainedContourSystem (G := G) b.1 x).ends

theorem cmp99SourceUbarGamma1_length_le (b : PhysicalBond d N')
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' b.1) :
    (cmp99SourceUbarGamma1 (G := G) b x).length ≤ d * (M - 1) := by
  exact cmp99BlockContainedContourSystem_length_le (G := G) b.1 x hx

theorem cmp99SourceUbarGamma2_path (b : PhysicalBond d N')
    (x : FinBox d (M * N')) :
    IsPathFrom (G := G) x (cmp99SourceUbarGamma2 (G := G) b x) :=
  (cmp99SourceParallelTransportPath (G := G) x b.2).isPath

theorem cmp99SourceUbarGamma2_end (b : PhysicalBond d N')
    (x : FinBox d (M * N')) :
    pathEnd (G := G) x (cmp99SourceUbarGamma2 (G := G) b x) =
      cmp99SourceTranslatedSite x b.2 :=
  (cmp99SourceParallelTransportPath (G := G) x b.2).ends

theorem cmp99SourceUbarGamma2_length (b : PhysicalBond d N')
    (x : FinBox d (M * N')) :
    (cmp99SourceUbarGamma2 (G := G) b x).length = M :=
  cmp99SourceParallelTransportPath_length (G := G) x b.2

theorem cmp99SourceUbarGamma2_length_le (hd : 2 ≤ d) (hM : 2 ≤ M)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    (cmp99SourceUbarGamma2 (G := G) b x).length ≤ d * (M - 1) := by
  rw [cmp99SourceUbarGamma2_length (G := G)]
  have hfirst : M ≤ 2 * (M - 1) := by omega
  have hsecond : 2 * (M - 1) ≤ d * (M - 1) :=
    Nat.mul_le_mul_right (M - 1) hd
  exact hfirst.trans hsecond

theorem cmp99SourceUbarGamma3_path (b : PhysicalBond d N')
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' b.1) :
    IsPathFrom (G := G)
      (pathEnd (G := G) x (cmp99SourceUbarGamma2 (G := G) b x))
      (cmp99SourceUbarGamma3 (G := G) b x) := by
  have hx' := cmp99SourceTranslatedSite_mem_targetBlock b.1 b.2 x hx
  rw [cmp99SourceUbarGamma2_end (G := G) b x]
  simp only [cmp99SourceUbarGamma3, dif_pos hx]
  exact ((concreteCMP99BlockContour (G := G) (b.1.shift b.2)
    ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).path.symm).isPath

theorem cmp99SourceUbarGamma3_end (b : PhysicalBond d N')
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' b.1) :
    pathEnd (G := G)
      (pathEnd (G := G) x (cmp99SourceUbarGamma2 (G := G) b x))
      (cmp99SourceUbarGamma3 (G := G) b x) =
        blockBasepoint M N' (b.1.shift b.2) := by
  have hx' := cmp99SourceTranslatedSite_mem_targetBlock b.1 b.2 x hx
  rw [cmp99SourceUbarGamma2_end (G := G) b x]
  simp only [cmp99SourceUbarGamma3, dif_pos hx]
  exact ((concreteCMP99BlockContour (G := G) (b.1.shift b.2)
    ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).path.symm).ends

theorem cmp99SourceUbarGamma3_length_le (b : PhysicalBond d N')
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' b.1) :
    (cmp99SourceUbarGamma3 (G := G) b x).length ≤ d * (M - 1) := by
  have hx' := cmp99SourceTranslatedSite_mem_targetBlock b.1 b.2 x hx
  simp only [cmp99SourceUbarGamma3, dif_pos hx,
    OrientedLatticePath.symm, reverseLatticePath, List.length_reverse,
    List.length_map]
  exact (concreteCMP99BlockContour (G := G) (b.1.shift b.2)
    ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).length_le

end

end YangMills.RG
