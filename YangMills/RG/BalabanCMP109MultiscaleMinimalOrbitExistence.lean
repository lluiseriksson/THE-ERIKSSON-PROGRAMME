/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109MinimalOrbitExistence
import YangMills.RG.ConcreteGaugeRGSupport

/-!
# A finite-volume multiscale variational background for CMP109

This file iterates the literal `2M -> M` block map and its proved right
inverse.  It constructs a full-depth map from `towerSize M₀ n` to `M₀`,
proves every full-depth fiber compact and nonempty, and proves that the exact
Wilson action attains its minimum on that fiber.

The construction is still weaker than the source regular-orbit theorem.  It
does not prove uniqueness modulo gauge, select the source axial-gauge
representative, or establish analytic dependence on the coarse background.
Consequently it is not yet the producer of the CMP109 (1.18) estimate or of
the residual `V''_k`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open YangMills GaugeConfig
open scoped BigOperators

noncomputable section

variable {d M₀ : ℕ} [NeZero d] [NeZero M₀]
variable {G : Type*} [Group G] [MeasurableSpace G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Full-depth block map, written by a recursion whose source and target
scales are definitionally transparent. -/
noncomputable def cmp109FullBlockMap (M₀ : ℕ) [NeZero M₀] :
    (n : ℕ) → GaugeConfig d (towerSize M₀ n) G → GaugeConfig d M₀ G
  | 0 => id
  | n + 1 =>
      cmp109FullBlockMap M₀ n ∘ blockMap (towerSize M₀ n)

/-- A literal multiscale right inverse obtained by lifting one scale at a
time. -/
noncomputable def cmp109FullBlockLift (M₀ : ℕ) [NeZero M₀] :
    (n : ℕ) → GaugeConfig d M₀ G → GaugeConfig d (towerSize M₀ n) G
  | 0 => id
  | n + 1 =>
      cmp109OneStepBlockLiftBackground (M := towerSize M₀ n) ∘
        cmp109FullBlockLift M₀ n

@[simp]
theorem cmp109FullBlockMap_lift (M₀ : ℕ) [NeZero M₀] :
    ∀ (n : ℕ) (V : GaugeConfig d M₀ G),
      cmp109FullBlockMap M₀ n (cmp109FullBlockLift M₀ n V) = V
  | 0, _ => rfl
  | n + 1, V => by
      change
        cmp109FullBlockMap M₀ n
            (blockMap (towerSize M₀ n)
              (cmp109OneStepBlockLiftBackground
                (M := towerSize M₀ n)
                (cmp109FullBlockLift M₀ n V))) =
          V
      rw [blockMap_cmp109OneStepBlockLiftBackground]
      exact cmp109FullBlockMap_lift M₀ n V

/-- Positive-coordinate expression of the full-depth map. -/
noncomputable def cmp109FullBlockCoordinates (M₀ : ℕ) [NeZero M₀]
    (n : ℕ) (x : PosEdge d (towerSize M₀ n) → G) :
    PosEdge d M₀ → G :=
  configToPos (cmp109FullBlockMap M₀ n (gaugeConfigEquiv x))

theorem continuous_cmp109FullBlockCoordinates (M₀ : ℕ) [NeZero M₀] :
    ∀ n : ℕ,
      Continuous
        (cmp109FullBlockCoordinates (d := d) (G := G) M₀ n)
  | 0 => by
      convert
        (continuous_id :
          Continuous (id : (PosEdge d M₀ → G) → (PosEdge d M₀ → G))) using 1
      funext x
      exact (gaugeConfigEquiv
        (d := d) (N := M₀) (G := G)).left_inv x
  | n + 1 => by
      have hcomp :=
        (continuous_cmp109FullBlockCoordinates M₀ n).comp
          (continuous_cmp109OneStepBlockCoordinates
            (d := d) (M := towerSize M₀ n) (G := G))
      simpa only [cmp109FullBlockCoordinates, cmp109FullBlockMap,
        Function.comp_apply,
        cmp109OneStepBlockCoordinates_eq_configToPos_blockMap] using hcomp

/-- Full-depth positive-coordinate fiber over a prescribed coarse
background. -/
def cmp109FullBlockFiber (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (V : GaugeConfig d M₀ G) :
    Set (PosEdge d (towerSize M₀ n) → G) :=
  {x | cmp109FullBlockCoordinates M₀ n x = configToPos V}

theorem isClosed_cmp109FullBlockFiber [T2Space G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ) (V : GaugeConfig d M₀ G) :
    IsClosed (cmp109FullBlockFiber (d := d) (G := G) M₀ n V) := by
  exact isClosed_singleton.preimage
    (continuous_cmp109FullBlockCoordinates M₀ n)

theorem isCompact_cmp109FullBlockFiber [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ) (V : GaugeConfig d M₀ G) :
    IsCompact (cmp109FullBlockFiber (d := d) (G := G) M₀ n V) :=
  (isClosed_cmp109FullBlockFiber M₀ n V).isCompact

theorem nonempty_cmp109FullBlockFiber
    (M₀ : ℕ) [NeZero M₀] (n : ℕ) (V : GaugeConfig d M₀ G) :
    (cmp109FullBlockFiber (d := d) (G := G) M₀ n V).Nonempty := by
  refine ⟨configToPos (cmp109FullBlockLift M₀ n V), ?_⟩
  have hround :
      gaugeConfigEquiv (configToPos (cmp109FullBlockLift M₀ n V)) =
        cmp109FullBlockLift M₀ n V :=
    (gaugeConfigEquiv
      (d := d) (N := towerSize M₀ n) (G := G)).right_inv _
  change
    configToPos
        (cmp109FullBlockMap M₀ n
          (gaugeConfigEquiv (configToPos (cmp109FullBlockLift M₀ n V)))) =
      configToPos V
  rw [hround]
  rw [cmp109FullBlockMap_lift]

/-- Wilson action at an arbitrary finite tower size, pulled back to positive
coordinates. -/
noncomputable def cmp109WilsonActionCoordinates
    {N : ℕ} [NeZero N] (plaquetteEnergy : G → ℝ)
    (x : PosEdge d N → G) : ℝ :=
  wilsonAction plaquetteEnergy (gaugeConfigEquiv x)

theorem continuous_cmp109GaugeConfigCoordinateAt
    {N : ℕ} [NeZero N] (e : ConcreteEdge d N) :
    Continuous (fun x : PosEdge d N → G => (gaugeConfigEquiv x) e) := by
  change Continuous (fun x : PosEdge d N → G => posToFun x e)
  unfold posToFun
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).inv

theorem continuous_cmp109PlaquetteHolonomyCoordinatesAt
    {N : ℕ} [NeZero N] (p : ConcretePlaquette d N) :
    Continuous (fun x : PosEdge d N → G =>
      plaquetteHolonomy (gaugeConfigEquiv x) p) := by
  unfold plaquetteHolonomy
  exact
    (((continuous_cmp109GaugeConfigCoordinateAt
      (G := G) (p.edges 0)).mul
      (continuous_cmp109GaugeConfigCoordinateAt
        (G := G) (p.edges 1))).mul
      (continuous_cmp109GaugeConfigCoordinateAt
        (G := G) (p.edges 2))).mul
      (continuous_cmp109GaugeConfigCoordinateAt
        (G := G) (p.edges 3))

theorem continuous_cmp109WilsonActionCoordinates
    {N : ℕ} [NeZero N]
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy) :
    Continuous
      (cmp109WilsonActionCoordinates
        (d := d) (N := N) (G := G) plaquetteEnergy) := by
  unfold cmp109WilsonActionCoordinates wilsonAction
  apply continuous_finset_sum
  intro p hp
  exact henergy.comp
    (continuous_cmp109PlaquetteHolonomyCoordinatesAt (G := G) p)

theorem exists_cmp109FullWilsonMinimizer
    [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M₀ G) :
    ∃ x ∈ cmp109FullBlockFiber (d := d) (G := G) M₀ n V,
      IsMinOn
        (cmp109WilsonActionCoordinates
          (d := d) (N := towerSize M₀ n) (G := G) plaquetteEnergy)
        (cmp109FullBlockFiber (d := d) (G := G) M₀ n V) x := by
  exact
    (isCompact_cmp109FullBlockFiber M₀ n V).exists_isMinOn
      (nonempty_cmp109FullBlockFiber M₀ n V)
      (continuous_cmp109WilsonActionCoordinates
        (d := d) (N := towerSize M₀ n) (G := G)
        plaquetteEnergy henergy).continuousOn

/-- Chosen finite-volume multiscale minimizer on the exact full-depth block
fiber. -/
noncomputable def cmp109FullMinimalCoordinates
    [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M₀ G) : PosEdge d (towerSize M₀ n) → G :=
  (exists_cmp109FullWilsonMinimizer M₀ n plaquetteEnergy henergy V).choose

theorem cmp109FullMinimalCoordinates_mem_fiber
    [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M₀ G) :
    cmp109FullMinimalCoordinates M₀ n plaquetteEnergy henergy V ∈
      cmp109FullBlockFiber (d := d) (G := G) M₀ n V :=
  (exists_cmp109FullWilsonMinimizer
    M₀ n plaquetteEnergy henergy V).choose_spec.1

theorem cmp109FullMinimalCoordinates_isMinOn
    [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M₀ G) :
    IsMinOn
      (cmp109WilsonActionCoordinates
        (d := d) (N := towerSize M₀ n) (G := G) plaquetteEnergy)
      (cmp109FullBlockFiber (d := d) (G := G) M₀ n V)
      (cmp109FullMinimalCoordinates M₀ n plaquetteEnergy henergy V) :=
  (exists_cmp109FullWilsonMinimizer
    M₀ n plaquetteEnergy henergy V).choose_spec.2

noncomputable def cmp109FullMinimalBackground
    [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M₀ G) : GaugeConfig d (towerSize M₀ n) G :=
  gaugeConfigEquiv
    (cmp109FullMinimalCoordinates M₀ n plaquetteEnergy henergy V)

theorem cmp109FullBlockMap_minimalBackground
    [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M₀ G) :
    cmp109FullBlockMap M₀ n
        (cmp109FullMinimalBackground M₀ n plaquetteEnergy henergy V) =
      V := by
  apply (gaugeConfigEquiv (d := d) (N := M₀) (G := G)).symm.injective
  exact cmp109FullMinimalCoordinates_mem_fiber
    M₀ n plaquetteEnergy henergy V

theorem cmp109FullMinimalBackground_minimal
    [T2Space G] [CompactSpace G]
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (plaquetteEnergy : G → ℝ) (henergy : Continuous plaquetteEnergy)
    (V : GaugeConfig d M₀ G)
    (U : GaugeConfig d (towerSize M₀ n) G)
    (hU : cmp109FullBlockMap M₀ n U = V) :
    wilsonAction plaquetteEnergy
        (cmp109FullMinimalBackground M₀ n plaquetteEnergy henergy V) ≤
      wilsonAction plaquetteEnergy U := by
  have hcoord :
      configToPos U ∈
        cmp109FullBlockFiber (d := d) (G := G) M₀ n V := by
    have hround :
        gaugeConfigEquiv (configToPos U) = U :=
      (gaugeConfigEquiv
        (d := d) (N := towerSize M₀ n) (G := G)).right_inv U
    change
      configToPos
          (cmp109FullBlockMap M₀ n
            (gaugeConfigEquiv (configToPos U))) =
        configToPos V
    rw [hround, hU]
  have hmin :=
    cmp109FullMinimalCoordinates_isMinOn
      M₀ n plaquetteEnergy henergy V hcoord
  change
    wilsonAction plaquetteEnergy
        (gaugeConfigEquiv
          (cmp109FullMinimalCoordinates M₀ n plaquetteEnergy henergy V)) ≤
      wilsonAction plaquetteEnergy U
  change
    wilsonAction plaquetteEnergy
        (gaugeConfigEquiv
          (cmp109FullMinimalCoordinates M₀ n plaquetteEnergy henergy V)) ≤
      wilsonAction plaquetteEnergy (gaugeConfigEquiv (configToPos U)) at hmin
  have hround :
      gaugeConfigEquiv (configToPos U) = U :=
    (gaugeConfigEquiv
      (d := d) (N := towerSize M₀ n) (G := G)).right_inv U
  rw [hround] at hmin
  exact hmin

section SUN

variable {Nc : ℕ} [NeZero Nc]

/-- Literal finite-volume multiscale `SU(Nc)` minimizer. -/
noncomputable def cmp109FullSUNMinimalBackground
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (V : PhysicalGaugeBackground d M₀ Nc) :
    PhysicalGaugeBackground d (towerSize M₀ n) Nc :=
  cmp109FullMinimalBackground M₀ n
    cmp109SUNWilsonPlaquetteEnergy
    continuous_cmp109SUNWilsonPlaquetteEnergy V

@[simp]
theorem cmp109FullBlockMap_cmp109FullSUNMinimalBackground
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (V : PhysicalGaugeBackground d M₀ Nc) :
    cmp109FullBlockMap M₀ n
        (cmp109FullSUNMinimalBackground M₀ n V) =
      V :=
  cmp109FullBlockMap_minimalBackground
    M₀ n cmp109SUNWilsonPlaquetteEnergy
    continuous_cmp109SUNWilsonPlaquetteEnergy V

theorem cmp109FullSUNMinimalBackground_minimal
    (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (V : PhysicalGaugeBackground d M₀ Nc)
    (U : PhysicalGaugeBackground d (towerSize M₀ n) Nc)
    (hU : cmp109FullBlockMap M₀ n U = V) :
    wilsonAction cmp109SUNWilsonPlaquetteEnergy
        (cmp109FullSUNMinimalBackground M₀ n V) ≤
      wilsonAction cmp109SUNWilsonPlaquetteEnergy U :=
  cmp109FullMinimalBackground_minimal
    M₀ n cmp109SUNWilsonPlaquetteEnergy
    continuous_cmp109SUNWilsonPlaquetteEnergy V U hU

end SUN

end

end YangMills.RG
