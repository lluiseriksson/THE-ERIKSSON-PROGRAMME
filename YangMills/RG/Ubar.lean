/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.BlockLattice
import YangMills.RG.BlockMaps
import YangMills.RG.HolonomyGauge
import YangMills.RG.NearLog
import YangMills.RG.MatrixRealization

/-!
# Gauge covariance of the coarse gauge-renormalization operator Ū (Target B4-Ū full)

This file defines the coarse gauge-renormalization operator `Ū` on the lattice and
proves its gauge covariance under a matrix representation.

Important convention: `nearLog Y` is the Mercator series for `log (1 + Y)`.
Therefore the small-field variable for a represented group element `D` is
`D - 1`, not `D` itself.  In Bałaban's CMP 109 (0.12) formula the logarithm is
applied to a near-identity deviation group element; the Lean series argument is
the deviation from the identity.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

/-- The deviation term for a coarse edge `C` at a fine site `x`.
    Formulated with orientation-consistent path cancellation. -/
def UbarDeviation {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G))) : G :=
  let W1 := wilsonLine A_fine (Γ_1 x)
  let W2 := wilsonLine A_fine (Γ_2 x)
  let W3 := wilsonLine A_fine (Γ_3 x)
  let W4 := A_coarse C
  W1 * W2 * W3 * W4⁻¹

/-- The coarse gauge-transformation restriction. -/
def coarseTransform {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] {L : ℕ} [NeZero L]
    (u : GaugeTransform d (L * N') G) : GaugeTransform d N' G :=
  fun y => u (blockBasepoint L N' y)

/-- The deviation conjugates by the source basepoint under gauge transformation. -/
theorem UbarDeviation_gaugeAct {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    (u : GaugeTransform d (L * N') G) (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (hpath1 : IsPathFrom (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x))
    (hend1 : pathEnd (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x) = x)
    (hpath2 : IsPathFrom x (Γ_2 x))
    (hpath3 : IsPathFrom (pathEnd x (Γ_2 x)) (Γ_3 x))
    (hend3 : pathEnd (pathEnd x (Γ_2 x)) (Γ_3 x) = blockBasepoint L N' (FiniteLatticeGeometry.dst C)) :
    UbarDeviation (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3
      = u (blockBasepoint L N' (FiniteLatticeGeometry.src C))
        * UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3
        * (u (blockBasepoint L N' (FiniteLatticeGeometry.src C)))⁻¹ := by
  let y_minus := blockBasepoint L N' (FiniteLatticeGeometry.src C)
  let x_C := pathEnd x (Γ_2 x)
  unfold UbarDeviation
  rw [wilsonLine_gaugeAct_path u A_fine (Γ_1 x) y_minus hpath1]
  rw [wilsonLine_gaugeAct_path u A_fine (Γ_2 x) x hpath2]
  rw [wilsonLine_gaugeAct_path u A_fine (Γ_3 x) x_C hpath3]
  rw [hend1, hend3]
  rw [gaugeAct_apply]
  dsimp only [coarseTransform, y_minus, x_C]
  group

lemma rep_UbarDeviation_gaugeAct {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [MatrixRealization G 𝔸]
    (u : GaugeTransform d (L * N') G) (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (hpath1 : IsPathFrom (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x))
    (hend1 : pathEnd (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x) = x)
    (hpath2 : IsPathFrom x (Γ_2 x))
    (hpath3 : IsPathFrom (pathEnd x (Γ_2 x)) (Γ_3 x))
    (hend3 : pathEnd (pathEnd x (Γ_2 x)) (Γ_3 x) = blockBasepoint L N' (FiniteLatticeGeometry.dst C)) :
    (MatrixRealization.rep (UbarDeviation (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3) : Units 𝔸)
      = MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.src C)))
        * MatrixRealization.rep (UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3)
        * (MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.src C))))⁻¹ := by
  rw [UbarDeviation_gaugeAct u A_fine A_coarse C x Γ_1 Γ_2 Γ_3 hpath1 hend1 hpath2 hpath3 hend3]
  simp only [map_mul, map_inv]

/-- Conjugating a near-identity group element subtracts the identity by
conjugating the deviation from the identity:
`u * D * u⁻¹ - 1 = u * (D - 1) * u⁻¹`. -/
lemma units_conj_sub_one {𝔸 : Type*} [NormedRing 𝔸] (u : 𝔸ˣ) (D : 𝔸) :
    u.val * D * u⁻¹.val - 1 = u.val * (D - 1) * u⁻¹.val := by
  rw [mul_sub, sub_mul]
  simp [mul_assoc]

/-- The actual Mercator-series argument for the `Ū` logarithm: the represented
deviation group element minus the identity.  `nearLog` computes `log(1 + Y)`,
so this is the faithful small-field variable corresponding to
`log(U(c₋,x)·U(x,x(c))⁻¹·U(x(c),c₊)·U(-c))` in CMP 109 (0.12). -/
noncomputable def UbarDeviationLogArg {d N' : ℕ} [NeZero N'] {G : Type*} [Group G]
    [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [MatrixRealization G 𝔸]
    (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G))) :
    𝔸 :=
  (MatrixRealization.rep (UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3) : Units 𝔸).val - 1

/-- If the represented physical group element has operator norm one, the old
small-field condition `‖D‖ < 1` is impossible.  Physical unitary matrix
realizations satisfy this calibration, so `Ū` must use `D - 1` as its
small-field variable. -/
theorem represented_group_element_norm_lt_one_impossible_of_norm_eq_one
    {G : Type*} [Group G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [MatrixRealization G 𝔸] (g : G)
    (hunit : ‖(MatrixRealization.rep g : Units 𝔸).val‖ = 1) :
    ¬ ‖(MatrixRealization.rep g : Units 𝔸).val‖ < 1 := by
  rw [hunit]
  exact not_lt_of_ge le_rfl

/-- The corrected small-field premise is inhabited at the identity deviation:
if the path/coarse mismatch is exactly the identity group element, then the
Mercator argument is `0`. -/
theorem UbarDeviationLogArg_eq_zero_of_deviation_eq_one {d N' : ℕ} [NeZero N']
    {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [MatrixRealization G 𝔸]
    (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (h : UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3 = 1) :
    UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3 = 0 := by
  dsimp [UbarDeviationLogArg]
  rw [h]
  simp

/-- The corrected small-field premise is non-vacuous at exact matching
deviation. -/
theorem UbarDeviationLogArg_small_of_deviation_eq_one {d N' : ℕ} [NeZero N']
    {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [MatrixRealization G 𝔸]
    (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (h : UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3 = 1) :
    ‖UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3‖ < 1 := by
  rw [UbarDeviationLogArg_eq_zero_of_deviation_eq_one
    (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3 h]
  simp

/-- The represented Mercator argument `D - 1` transforms by conjugation under a
gauge transformation. -/
lemma UbarDeviationLogArg_gaugeAct {d N' : ℕ} [NeZero N'] {G : Type*} [Group G]
    [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [MatrixRealization G 𝔸]
    (u : GaugeTransform d (L * N') G) (A_fine : GaugeConfig d (L * N') G)
    (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (hpath1 : IsPathFrom (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x))
    (hend1 : pathEnd (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x) = x)
    (hpath2 : IsPathFrom x (Γ_2 x))
    (hpath3 : IsPathFrom (pathEnd x (Γ_2 x)) (Γ_3 x))
    (hend3 : pathEnd (pathEnd x (Γ_2 x)) (Γ_3 x) = blockBasepoint L N' (FiniteLatticeGeometry.dst C)) :
    UbarDeviationLogArg (𝔸 := 𝔸) (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
        C x Γ_1 Γ_2 Γ_3
      = (MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.src C))) : Units 𝔸).val
        * UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3
        * (MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.src C))) : Units 𝔸)⁻¹.val := by
  let u_src : Units 𝔸 := MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.src C)))
  have h_eq := rep_UbarDeviation_gaugeAct (𝔸 := 𝔸) u A_fine A_coarse C x Γ_1 Γ_2 Γ_3
    hpath1 hend1 hpath2 hpath3 hend3
  have h_val := congrArg (fun (z : Units 𝔸) => z.val) h_eq
  simp only [Units.val_mul] at h_val
  dsimp [UbarDeviationLogArg]
  rw [h_val]
  simpa [u_src] using
    units_conj_sub_one u_src
      ((MatrixRealization.rep (UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3) : Units 𝔸).val)

/-- The coarse gauge-renormalization operator `Ū` (represented in the algebra `𝔸`).
The logarithm is fed the identity deviation `D - 1`, since `nearLog Y` is
`log(1 + Y)`. -/
noncomputable def Ubar {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [MatrixRealization G 𝔸]
    (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G))) : 𝔸 :=
  let y_minus := FiniteLatticeGeometry.src C
  let S := blockOf L N' y_minus
  let term_x := fun x => nearLog (UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3)
  let exponent := (L ^ d : ℝ)⁻¹ • ∑ x ∈ S, term_x x
  NormedSpace.exp exponent * (MatrixRealization.rep (A_coarse C) : Units 𝔸).val

/-- Gauge covariance of the abstract `Ū`-block on the lattice (Target B4-Ū flux). -/
theorem Ubar_gaugeAct {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [MatrixRealization G 𝔸] [NormedAlgebra ℚ 𝔸]
    (u : GaugeTransform d (L * N') G) (A_fine : GaugeConfig d (L * N') G) (A_coarse : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (hpath1 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), IsPathFrom (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x))
    (hend1 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), pathEnd (blockBasepoint L N' (FiniteLatticeGeometry.src C)) (Γ_1 x) = x)
    (hpath2 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), IsPathFrom x (Γ_2 x))
    (hpath3 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), IsPathFrom (pathEnd x (Γ_2 x)) (Γ_3 x))
    (hend3 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), pathEnd (pathEnd x (Γ_2 x)) (Γ_3 x) = blockBasepoint L N' (FiniteLatticeGeometry.dst C))
    (hY : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C),
      ‖UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3‖ < 1) :
    Ubar (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse) C Γ_1 Γ_2 Γ_3
      = (MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.src C))) : Units 𝔸).val
        * Ubar A_fine A_coarse C Γ_1 Γ_2 Γ_3
        * (MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.dst C))) : Units 𝔸)⁻¹.val := by
  let y_minus := FiniteLatticeGeometry.src C
  let S := blockOf L N' y_minus
  let u_src : Units 𝔸 := MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.src C)))
  let u_dst : Units 𝔸 := MatrixRealization.rep (u (blockBasepoint L N' (FiniteLatticeGeometry.dst C)))

  have h_dev : ∀ x ∈ S,
      UbarDeviationLogArg (𝔸 := 𝔸) (gaugeAct u A_fine)
          (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3
        = u_src.val * UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3
          * u_src⁻¹.val := by
    intro x hx
    exact UbarDeviationLogArg_gaugeAct (𝔸 := 𝔸) u A_fine A_coarse C x Γ_1 Γ_2 Γ_3
      (hpath1 x hx) (hend1 x hx) (hpath2 x hx) (hpath3 x hx) (hend3 x hx)

  have h_log : ∀ x ∈ S,
      nearLog (UbarDeviationLogArg (𝔸 := 𝔸) (gaugeAct u A_fine)
          (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3)
      = u_src.val * nearLog (UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3) * u_src⁻¹.val := by
    intro x hx
    rw [h_dev x hx]
    exact nearLog_conj u_src (hY x hx)

  have h_sum : ∑ x ∈ S, nearLog (UbarDeviationLogArg (𝔸 := 𝔸) (gaugeAct u A_fine)
        (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3)
      = u_src.val * (∑ x ∈ S, nearLog (UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3)) * u_src⁻¹.val := by
    have h_conj := nearLog_sum_smul_conj u_src S (fun _ => 1)
      (fun x => UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3) hY
    simp only [one_smul] at h_conj
    have h_rw : ∑ x ∈ S, nearLog (UbarDeviationLogArg (𝔸 := 𝔸) (gaugeAct u A_fine)
          (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3)
        = ∑ x ∈ S, nearLog (u_src.val *
            UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3 * u_src⁻¹.val) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [h_dev x hx]
    rw [h_rw]
    exact h_conj

  have h_exp_scale : (L ^ d : ℝ)⁻¹ • (∑ x ∈ S, nearLog
        (UbarDeviationLogArg (𝔸 := 𝔸) (gaugeAct u A_fine)
          (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3))
      = u_src.val * ((L ^ d : ℝ)⁻¹ • ∑ x ∈ S, nearLog
          (UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3)) * u_src⁻¹.val := by
    rw [h_sum, ← smul_mul_assoc, ← mul_smul_comm]

  have h_exp_conj : NormedSpace.exp ((L ^ d : ℝ)⁻¹ • ∑ x ∈ S, nearLog
        (UbarDeviationLogArg (𝔸 := 𝔸) (gaugeAct u A_fine)
          (gaugeAct (coarseTransform u) A_coarse) C x Γ_1 Γ_2 Γ_3))
      = u_src.val * NormedSpace.exp ((L ^ d : ℝ)⁻¹ • ∑ x ∈ S, nearLog
          (UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3)) * u_src⁻¹.val := by
    rw [h_exp_scale, NormedSpace.exp_units_conj]

  have h_coarse_gauge : (MatrixRealization.rep (coarseTransform u (FiniteLatticeGeometry.src C) * A_coarse C * (coarseTransform u (FiniteLatticeGeometry.dst C))⁻¹) : Units 𝔸).val
      = u_src.val * (MatrixRealization.rep (A_coarse C) : Units 𝔸).val * u_dst⁻¹.val := by
    simp only [map_mul, map_inv, Units.val_mul]
    rfl

  dsimp [Ubar]
  rw [h_exp_conj, h_coarse_gauge]
  simp only [mul_assoc]
  rw [← mul_assoc u_src⁻¹.val, Units.inv_mul u_src, one_mul]

theorem wilsonLine_congr {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
    (A A' : GaugeConfig d N G) (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))
    (h : ∀ e ∈ es, A e = A' e) :
    wilsonLine A es = wilsonLine A' es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [wilsonLine_cons, wilsonLine_cons]
    rw [h e (List.mem_cons_self)]
    rw [ih (fun e' he' => h e' (List.mem_cons_of_mem e he'))]

lemma UbarDeviation_congr {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    (A_fine A_fine' : GaugeConfig d (L * N') G) (A_coarse A_coarse' : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G)) (x : FinBox d (L * N'))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (h_coarse : A_coarse C = A_coarse' C)
    (h_fine1 : ∀ e ∈ Γ_1 x, A_fine e = A_fine' e)
    (h_fine2 : ∀ e ∈ Γ_2 x, A_fine e = A_fine' e)
    (h_fine3 : ∀ e ∈ Γ_3 x, A_fine e = A_fine' e) :
    UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3 = UbarDeviation A_fine' A_coarse' C x Γ_1 Γ_2 Γ_3 := by
  unfold UbarDeviation
  rw [wilsonLine_congr A_fine A_fine' (Γ_1 x) h_fine1]
  rw [wilsonLine_congr A_fine A_fine' (Γ_2 x) h_fine2]
  rw [wilsonLine_congr A_fine A_fine' (Γ_3 x) h_fine3]
  rw [h_coarse]

/-- **Locality of the coarse averaging operator Ū** (Target B5-full).
    If two fine gauge configurations agree on the fine paths inside the blocks
    adjacent to the coarse edge, and the coarse configurations agree on that coarse
    edge, then the coarse averaged fields are identical. -/
theorem Ubar_locality {d N' : ℕ} [NeZero N'] {G : Type*} [Group G] [FiniteLatticeGeometry d N' G]
    {L : ℕ} [NeZero L] [FiniteLatticeGeometry d (L * N') G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [MatrixRealization G 𝔸]
    (A_fine A_fine' : GaugeConfig d (L * N') G) (A_coarse A_coarse' : GaugeConfig d N' G)
    (C : FiniteLatticeGeometry.E (d := d) (N := N') (G := G))
    (Γ_1 Γ_2 Γ_3 : FinBox d (L * N') → List (FiniteLatticeGeometry.E (d := d) (N := L * N') (G := G)))
    (h_coarse : A_coarse C = A_coarse' C)
    (h_fine1 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), ∀ e ∈ Γ_1 x, A_fine e = A_fine' e)
    (h_fine2 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), ∀ e ∈ Γ_2 x, A_fine e = A_fine' e)
    (h_fine3 : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C), ∀ e ∈ Γ_3 x, A_fine e = A_fine' e) :
    (Ubar A_fine A_coarse C Γ_1 Γ_2 Γ_3 : 𝔸) = Ubar A_fine' A_coarse' C Γ_1 Γ_2 Γ_3 := by
  have h_sum : (∑ x ∈ blockOf L N' (FiniteLatticeGeometry.src C),
        nearLog (UbarDeviationLogArg (𝔸 := 𝔸) A_fine A_coarse C x Γ_1 Γ_2 Γ_3))
      = (∑ x ∈ blockOf L N' (FiniteLatticeGeometry.src C),
        nearLog (UbarDeviationLogArg (𝔸 := 𝔸) A_fine' A_coarse' C x Γ_1 Γ_2 Γ_3)) := by
    have h_dev : ∀ x ∈ blockOf L N' (FiniteLatticeGeometry.src C),
        UbarDeviation A_fine A_coarse C x Γ_1 Γ_2 Γ_3 = UbarDeviation A_fine' A_coarse' C x Γ_1 Γ_2 Γ_3 := by
      intro x hx
      exact UbarDeviation_congr A_fine A_fine' A_coarse A_coarse' C x Γ_1 Γ_2 Γ_3 h_coarse (h_fine1 x hx) (h_fine2 x hx) (h_fine3 x hx)
    refine Finset.sum_congr rfl (fun x hx => ?_)
    dsimp [UbarDeviationLogArg]
    rw [h_dev x hx]
  dsimp [Ubar]
  rw [h_sum, h_coarse]

end YangMills.RG
