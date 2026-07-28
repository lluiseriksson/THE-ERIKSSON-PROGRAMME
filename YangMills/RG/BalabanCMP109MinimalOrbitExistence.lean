/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.ConcreteGaugeRGFidelity
import YangMills.RG.PhysicalGaugeCochains
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# A literal one-step variational background for CMP109

CMP109 defines `U_k(V)` as a representative of the minimal orbit of the
Wilson action under the exact block constraint `M_k(U) = V`.  This file
constructs the finite-volume, one-step (`2M -> M`) variational problem in
positive-bond coordinates and proves existence of a minimizer.

This is not the later regular-orbit theorem: uniqueness modulo gauge,
selection of the axial-gauge representative, regularity in `V`, and the
multiscale map `U_k` remain open.  In particular the minimizer below is not
identified with a pointwise exponential variation.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open YangMills GaugeConfig
open scoped BigOperators

noncomputable section

variable {d M : ℕ} [NeZero d] [NeZero M]
variable {G : Type*} [Group G] [MeasurableSpace G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The even first fine bond underlying a positive coarse bond. -/
def cmp109FineEdgeAEmbed (e : PosEdge d M) : PosEdge d (2 * M) :=
  ⟨fineEdgeA e.1.source e.1.dir, rfl⟩

/-- The odd second fine bond underlying a positive coarse bond. -/
def cmp109FineEdgeBEmbed (e : PosEdge d M) : PosEdge d (2 * M) :=
  ⟨fineEdgeB e.1.source e.1.dir, rfl⟩

theorem cmp109FineEdgeAEmbed_injective :
    Function.Injective (cmp109FineEdgeAEmbed (d := d) (M := M)) := by
  rintro ⟨⟨y, i, sign⟩, hsign⟩ ⟨⟨z, j, sign'⟩, hsign'⟩ h
  cases sign <;> try contradiction
  cases sign' <;> try contradiction
  simp only [cmp109FineEdgeAEmbed, Subtype.mk.injEq,
    fineEdgeA, ConcreteEdge.mk.injEq] at h
  rcases h with ⟨hembed, hij, _⟩
  have hy : y = z := coarseSiteEmbed_injective hembed
  subst z
  cases hij
  rfl

theorem fineEdgeB_ne_fineEdgeA
    (y z : FinBox d M) (i j : Fin d) :
    fineEdgeB y i ≠ fineEdgeA z j := by
  intro h
  have hij : i = j := congrArg ConcreteEdge.dir h
  subst j
  have hs :
      (coarseSiteEmbed y).shift i = coarseSiteEmbed z :=
    congrArg ConcreteEdge.source h
  have hi := congrArg (fun x : FinBox d (2 * M) => (x i).val) hs
  simp only [FinBox.shift, if_pos, coarseSiteEmbed] at hi
  rw [Nat.mod_eq_of_lt (by
    have hy := (y i).isLt
    have hM := NeZero.pos M
    omega : 2 * (y i).val + 1 < 2 * M)] at hi
  omega

/-- A literal right inverse of the one-step group-valued block map: prescribed
coarse holonomy is placed on the first fine bond and the second fine bond is
the identity. -/
noncomputable def cmp109OneStepBlockLiftCoordinates
    (V : GaugeConfig d M G) : PosEdge d (2 * M) → G :=
  Function.extend
    (cmp109FineEdgeAEmbed (d := d) (M := M))
    (configToPos V)
    (fun _ => 1)

@[simp]
theorem cmp109OneStepBlockLiftCoordinates_apply_A
    (V : GaugeConfig d M G) (e : PosEdge d M) :
    cmp109OneStepBlockLiftCoordinates (d := d) (M := M) V
        (cmp109FineEdgeAEmbed e) =
      configToPos V e := by
  exact cmp109FineEdgeAEmbed_injective.extend_apply _ _ e

@[simp]
theorem cmp109OneStepBlockLiftCoordinates_apply_B
    (V : GaugeConfig d M G) (e : PosEdge d M) :
    cmp109OneStepBlockLiftCoordinates (d := d) (M := M) V
        (cmp109FineEdgeBEmbed e) = 1 := by
  apply Function.extend_apply'
  rintro ⟨e', h⟩
  exact fineEdgeB_ne_fineEdgeA e.1.source e'.1.source e.1.dir e'.1.dir
    (congrArg Subtype.val h.symm)

/-- The literal positive-edge coordinate form of the `2M -> M` block map. -/
noncomputable def cmp109OneStepBlockCoordinates
    (x : PosEdge d (2 * M) → G) : PosEdge d M → G :=
  fun e =>
    x ⟨fineEdgeA e.1.source e.1.dir, rfl⟩ *
      x ⟨fineEdgeB e.1.source e.1.dir, rfl⟩

theorem continuous_cmp109OneStepBlockCoordinates :
    Continuous
      (cmp109OneStepBlockCoordinates (d := d) (M := M) (G := G)) := by
  apply continuous_pi
  intro e
  exact (continuous_apply _).mul (continuous_apply _)

/-- The positive coordinates agree exactly with the concrete block map. -/
theorem cmp109OneStepBlockCoordinates_eq_configToPos_blockMap
    (x : PosEdge d (2 * M) → G) :
    cmp109OneStepBlockCoordinates (d := d) (M := M) x =
      configToPos (blockMap M (gaugeConfigEquiv x)) := by
  funext e
  rcases e with ⟨⟨y, i, sign⟩, hsign⟩
  cases sign
  · contradiction
  · exact (blockMap_apply_pos M (gaugeConfigEquiv x) y i).symm

@[simp]
theorem cmp109OneStepBlockCoordinates_lift
    (V : GaugeConfig d M G) :
    cmp109OneStepBlockCoordinates (d := d) (M := M)
        (cmp109OneStepBlockLiftCoordinates V) =
      configToPos V := by
  funext e
  simp only [cmp109OneStepBlockCoordinates]
  change
    cmp109OneStepBlockLiftCoordinates V (cmp109FineEdgeAEmbed e) *
        cmp109OneStepBlockLiftCoordinates V (cmp109FineEdgeBEmbed e) =
      configToPos V e
  rw [cmp109OneStepBlockLiftCoordinates_apply_A,
    cmp109OneStepBlockLiftCoordinates_apply_B, mul_one]

/-- Positive-coordinate fiber of the exact one-step block constraint. -/
def cmp109OneStepBlockFiber (V : GaugeConfig d M G) :
    Set (PosEdge d (2 * M) → G) :=
  {x | cmp109OneStepBlockCoordinates (d := d) (M := M) x = configToPos V}

theorem isClosed_cmp109OneStepBlockFiber [T2Space G]
    (V : GaugeConfig d M G) :
    IsClosed (cmp109OneStepBlockFiber (d := d) (M := M) V) := by
  exact isClosed_singleton.preimage continuous_cmp109OneStepBlockCoordinates

theorem isCompact_cmp109OneStepBlockFiber [T2Space G] [CompactSpace G]
    (V : GaugeConfig d M G) :
    IsCompact (cmp109OneStepBlockFiber (d := d) (M := M) V) :=
  (isClosed_cmp109OneStepBlockFiber (d := d) (M := M) V).isCompact

theorem nonempty_cmp109OneStepBlockFiber
    (V : GaugeConfig d M G) :
    (cmp109OneStepBlockFiber (d := d) (M := M) V).Nonempty := by
  exact ⟨cmp109OneStepBlockLiftCoordinates V,
    cmp109OneStepBlockCoordinates_lift V⟩

/-- Evaluation of a full gauge configuration reconstructed from positive
coordinates is continuous at every fixed oriented edge. -/
theorem continuous_cmp109GaugeConfigCoordinate
    (e : ConcreteEdge d (2 * M)) :
    Continuous (fun x : PosEdge d (2 * M) → G => (gaugeConfigEquiv x) e) := by
  change Continuous (fun x : PosEdge d (2 * M) → G => posToFun x e)
  unfold posToFun
  split_ifs with h
  · exact continuous_apply _
  · exact (continuous_apply _).inv

theorem continuous_cmp109PlaquetteHolonomyCoordinates
    (p : ConcretePlaquette d (2 * M)) :
    Continuous (fun x : PosEdge d (2 * M) → G =>
      plaquetteHolonomy (gaugeConfigEquiv x) p) := by
  unfold plaquetteHolonomy
  exact
    (((continuous_cmp109GaugeConfigCoordinate
      (M := M) (G := G) (p.edges 0)).mul
      (continuous_cmp109GaugeConfigCoordinate
        (M := M) (G := G) (p.edges 1))).mul
      (continuous_cmp109GaugeConfigCoordinate
        (M := M) (G := G) (p.edges 2))).mul
      (continuous_cmp109GaugeConfigCoordinate
        (M := M) (G := G) (p.edges 3))

/-- The exact Wilson action pulled back to positive-edge coordinates. -/
noncomputable def cmp109OneStepWilsonAction
    (plaquetteEnergy : G → ℝ)
    (x : PosEdge d (2 * M) → G) : ℝ :=
  wilsonAction plaquetteEnergy (gaugeConfigEquiv x)

theorem continuous_cmp109OneStepWilsonAction
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy) :
    Continuous
      (cmp109OneStepWilsonAction (d := d) (M := M) plaquetteEnergy) := by
  unfold cmp109OneStepWilsonAction wilsonAction
  apply continuous_finset_sum
  intro p hp
  exact henergy.comp
    (continuous_cmp109PlaquetteHolonomyCoordinates (M := M) (G := G) p)

/-- Existence of a minimum of the literal Wilson action on every nonempty
one-step block fiber. -/
theorem exists_cmp109OneStepWilsonMinimizer
    [T2Space G] [CompactSpace G]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M G) :
    ∃ x ∈ cmp109OneStepBlockFiber (d := d) (M := M) V,
      IsMinOn
        (cmp109OneStepWilsonAction (d := d) (M := M) plaquetteEnergy)
        (cmp109OneStepBlockFiber (d := d) (M := M) V) x := by
  exact
    (isCompact_cmp109OneStepBlockFiber (d := d) (M := M) V).exists_isMinOn
      (nonempty_cmp109OneStepBlockFiber (d := d) (M := M) V)
      (continuous_cmp109OneStepWilsonAction
        (d := d) (M := M) plaquetteEnergy henergy).continuousOn

/-- A fixed representative of the finite-volume one-step variational
minimum.  The definition chooses from the proved compact minimum; it does not
claim uniqueness of the minimizing gauge orbit. -/
noncomputable def cmp109OneStepMinimalCoordinates
    [T2Space G] [CompactSpace G]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M G) : PosEdge d (2 * M) → G :=
  (exists_cmp109OneStepWilsonMinimizer
    (d := d) (M := M) plaquetteEnergy henergy V).choose

theorem cmp109OneStepMinimalCoordinates_mem_fiber
    [T2Space G] [CompactSpace G]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M G) :
    cmp109OneStepMinimalCoordinates
        (d := d) (M := M) plaquetteEnergy henergy V ∈
      cmp109OneStepBlockFiber (d := d) (M := M) V :=
  (exists_cmp109OneStepWilsonMinimizer
    (d := d) (M := M) plaquetteEnergy henergy V).choose_spec.1

theorem cmp109OneStepMinimalCoordinates_isMinOn
    [T2Space G] [CompactSpace G]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M G) :
    IsMinOn
      (cmp109OneStepWilsonAction (d := d) (M := M) plaquetteEnergy)
      (cmp109OneStepBlockFiber (d := d) (M := M) V)
      (cmp109OneStepMinimalCoordinates
        (d := d) (M := M) plaquetteEnergy henergy V) :=
  (exists_cmp109OneStepWilsonMinimizer
    (d := d) (M := M) plaquetteEnergy henergy V).choose_spec.2

/-- The literal group-valued one-step minimal background. -/
noncomputable def cmp109OneStepMinimalBackground
    [T2Space G] [CompactSpace G]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M G) : GaugeConfig d (2 * M) G :=
  gaugeConfigEquiv
    (cmp109OneStepMinimalCoordinates
      (d := d) (M := M) plaquetteEnergy henergy V)

/-- The chosen minimal background lies on the exact block fiber. -/
theorem blockMap_cmp109OneStepMinimalBackground
    [T2Space G] [CompactSpace G]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M G) :
    blockMap M
        (cmp109OneStepMinimalBackground
          (d := d) (M := M) plaquetteEnergy henergy V) =
      V := by
  apply (gaugeConfigEquiv (d := d) (N := M) (G := G)).symm.injective
  change
    configToPos
        (blockMap M
          (gaugeConfigEquiv
            (cmp109OneStepMinimalCoordinates
              (d := d) (M := M) plaquetteEnergy henergy V))) =
      configToPos V
  rw [← cmp109OneStepBlockCoordinates_eq_configToPos_blockMap]
  exact cmp109OneStepMinimalCoordinates_mem_fiber
    (d := d) (M := M) plaquetteEnergy henergy V

/-- Source-facing minimality: among every group-valued fine background with
the same exact block image, the chosen background minimizes the Wilson
action. -/
theorem cmp109OneStepMinimalBackground_minimal
    [T2Space G] [CompactSpace G]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M G)
    (U : GaugeConfig d (2 * M) G) (hU : blockMap M U = V) :
    wilsonAction plaquetteEnergy
        (cmp109OneStepMinimalBackground
          (d := d) (M := M) plaquetteEnergy henergy V) ≤
      wilsonAction plaquetteEnergy U := by
  have hcoord :
      configToPos U ∈ cmp109OneStepBlockFiber (d := d) (M := M) V := by
    have hround :
        gaugeConfigEquiv (configToPos U) = U :=
      (gaugeConfigEquiv
        (d := d) (N := 2 * M) (G := G)).right_inv U
    change
      cmp109OneStepBlockCoordinates (configToPos U) = configToPos V
    rw [cmp109OneStepBlockCoordinates_eq_configToPos_blockMap,
      hround, hU]
  have hmin :=
    cmp109OneStepMinimalCoordinates_isMinOn
      (d := d) (M := M) plaquetteEnergy henergy V hcoord
  change
    wilsonAction plaquetteEnergy
        (gaugeConfigEquiv
          (cmp109OneStepMinimalCoordinates
            (d := d) (M := M) plaquetteEnergy henergy V)) ≤
      wilsonAction plaquetteEnergy U
  change
    wilsonAction plaquetteEnergy
        (gaugeConfigEquiv
          (cmp109OneStepMinimalCoordinates
            (d := d) (M := M) plaquetteEnergy henergy V)) ≤
      wilsonAction plaquetteEnergy (gaugeConfigEquiv (configToPos U)) at hmin
  have hround :
      gaugeConfigEquiv (configToPos U) = U :=
    (gaugeConfigEquiv
      (d := d) (N := 2 * M) (G := G)).right_inv U
  rw [hround] at hmin
  exact hmin

section SUN

variable {Nc : ℕ} [NeZero Nc]

/-- Wilson plaquette energy on the literal compact `SU(Nc)` background
space, in the same `1 - Re tr` convention used by the Hessian campaign. -/
def cmp109SUNWilsonPlaquetteEnergy (U : SUN Nc) : ℝ :=
  1 - (Matrix.trace U.val).re

theorem continuous_cmp109SUNWilsonPlaquetteEnergy :
    Continuous (cmp109SUNWilsonPlaquetteEnergy (Nc := Nc)) := by
  unfold cmp109SUNWilsonPlaquetteEnergy
  exact continuous_const.sub
    (Complex.reCLM.continuous.comp
      continuous_subtype_val.matrix_trace)

/-- The concrete one-step `SU(Nc)` minimal background.  No action, compactness
certificate, block-fiber witness, or minimizer is supplied by the caller. -/
noncomputable def cmp109OneStepSUNMinimalBackground
    (V : PhysicalGaugeBackground d M Nc) :
    PhysicalGaugeBackground d (2 * M) Nc :=
  cmp109OneStepMinimalBackground
    cmp109SUNWilsonPlaquetteEnergy
    continuous_cmp109SUNWilsonPlaquetteEnergy V

@[simp]
theorem blockMap_cmp109OneStepSUNMinimalBackground
    (V : PhysicalGaugeBackground d M Nc) :
    blockMap M (cmp109OneStepSUNMinimalBackground V) = V :=
  blockMap_cmp109OneStepMinimalBackground
    cmp109SUNWilsonPlaquetteEnergy
    continuous_cmp109SUNWilsonPlaquetteEnergy V

theorem cmp109OneStepSUNMinimalBackground_minimal
    (V : PhysicalGaugeBackground d M Nc)
    (U : PhysicalGaugeBackground d (2 * M) Nc)
    (hU : blockMap M U = V) :
    wilsonAction cmp109SUNWilsonPlaquetteEnergy
        (cmp109OneStepSUNMinimalBackground V) ≤
      wilsonAction cmp109SUNWilsonPlaquetteEnergy U :=
  cmp109OneStepMinimalBackground_minimal
    cmp109SUNWilsonPlaquetteEnergy
    continuous_cmp109SUNWilsonPlaquetteEnergy V U hU

end SUN

end

end YangMills.RG
