/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99BlockContour
import YangMills.RG.PhysicalGaugeCochains

/-!
# Covariant path control for the CMP99 source average

The source average transports a zero-cochain along literal block-contained
contours.  This file proves the exact deterministic bridge from those
transports to the physical covariant derivative: the endpoint defect along a
path is bounded by the sum of the covariant edge defects on that path.

This is the pathwise ingredient of the source block-Poincare estimate.  No
Poincare constant or coercivity conclusion is assumed here.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Covariant zero-cochain defect on an arbitrarily oriented physical edge. -/
noncomputable def covariantEdgeDefect
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc)
    (e : ConcreteEdge d N) : SUNLieCoord Nc :=
  phi e.srcV - rho.adCLM (U e) (phi e.dstV)

/-- The oriented edge defect is literally the oriented value of `D_U phi`. -/
theorem covariantEdgeDefect_eq_orientedOneValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc)
    (e : ConcreteEdge d N) :
    covariantEdgeDefect rho U phi e =
      orientedOneValue rho U (covariantD0CLM rho U phi) e := by
  cases e with
  | mk x i sign =>
      cases sign with
      | false =>
          simp only [covariantEdgeDefect, ConcreteEdge.srcV,
            ConcreteEdge.dstV, orientedOneValue_neg,
            covariantD0CLM_apply]
          have hU :
              U (ConcreteEdge.mk x i false) =
                (U (ConcreteEdge.mk x i true))⁻¹ := by
            simpa [edgeFlip] using
              (U.map_reverse (ConcreteEdge.mk x i true))
          rw [hU, ContinuousLinearMap.map_sub,
            rho.ad_inv_apply_ad]
          simp only [Bool.false_eq_true, if_false]
          abel
      | true =>
          simp [covariantEdgeDefect, ConcreteEdge.srcV,
            ConcreteEdge.dstV, orientedOneValue]

/-- Reversing an edge does not change the norm of its covariant defect. -/
theorem norm_covariantEdgeDefect_eq
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc)
    (e : ConcreteEdge d N) :
    ‖covariantEdgeDefect rho U phi e‖ =
      ‖covariantD0CLM rho U phi (physicalBondOfEdge e)‖ := by
  rw [covariantEdgeDefect_eq_orientedOneValue]
  cases e with
  | mk x i sign =>
      cases sign with
      | false =>
          rw [orientedOneValue_neg, norm_neg, rho.norm_ad]
          rfl
      | true =>
          rw [orientedOneValue_pos]
          rfl

/-- Pathwise covariant telescoping in norm.  The holonomy order is the source
order used by the CMP99 contour average. -/
theorem norm_covariantPathDefect_le_sum
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc) :
    ∀ (es : List (ConcreteEdge d N)) (a : FinBox d N),
      IsPathFrom (G := SUN Nc) a es →
      ‖phi a - rho.adCLM (wilsonLine U es)
          (phi (pathEnd (G := SUN Nc) a es))‖ ≤
        (es.map (fun e => ‖covariantEdgeDefect rho U phi e‖)).sum := by
  intro es
  induction es with
  | nil =>
      intro a _hpath
      change ‖phi a - rho.adCLM 1 (phi a)‖ ≤ 0
      rw [rho.ad_one_apply]
      simp
  | cons e es ih =>
      intro a hpath
      obtain ⟨hsrc, hrest⟩ := hpath
      have htail := ih e.dstV hrest
      have hsplit :
          phi a - rho.adCLM (wilsonLine U (e :: es))
              (phi (pathEnd (G := SUN Nc) a (e :: es))) =
            covariantEdgeDefect rho U phi e +
              rho.adCLM (U e)
                (phi e.dstV -
                  rho.adCLM (wilsonLine U es)
                    (phi (pathEnd (G := SUN Nc) e.dstV es))) := by
        rw [wilsonLine_cons, pathEnd_cons, ← hsrc]
        simp only [covariantEdgeDefect, rho.ad_mul,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_sub]
        abel
      rw [hsplit]
      calc
        ‖covariantEdgeDefect rho U phi e +
            rho.adCLM (U e)
              (phi e.dstV -
                rho.adCLM (wilsonLine U es)
                  (phi (pathEnd (G := SUN Nc) e.dstV es)))‖ ≤
            ‖covariantEdgeDefect rho U phi e‖ +
              ‖rho.adCLM (U e)
                (phi e.dstV -
                  rho.adCLM (wilsonLine U es)
                    (phi (pathEnd (G := SUN Nc) e.dstV es)))‖ :=
          norm_add_le _ _
        _ = ‖covariantEdgeDefect rho U phi e‖ +
              ‖phi e.dstV -
                rho.adCLM (wilsonLine U es)
                  (phi (pathEnd (G := SUN Nc) e.dstV es))‖ := by
          rw [rho.norm_ad]
        _ ≤ ‖covariantEdgeDefect rho U phi e‖ +
              (es.map (fun e => ‖covariantEdgeDefect rho U phi e‖)).sum :=
          add_le_add_right htail _
        _ = ((e :: es).map
              (fun e => ‖covariantEdgeDefect rho U phi e‖)).sum := by
          simp

/-- A path of length `ell` costs at most `ell * ‖D_U phi‖`.  This bound is
volume-independent and applies in particular to every certified source block
contour. -/
theorem norm_covariantPathDefect_le_length_mul
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc)
    {GammaStart GammaEnd : FinBox d N}
    (Gamma : OrientedLatticePath (G := SUN Nc)
      (a := GammaStart) (b := GammaEnd)) :
    ‖phi GammaStart - rho.adCLM (Gamma.holonomy U) (phi GammaEnd)‖ ≤
      Gamma.edges.length * ‖covariantD0CLM rho U phi‖ := by
  have hpath := norm_covariantPathDefect_le_sum rho U phi
    Gamma.edges GammaStart Gamma.isPath
  rw [Gamma.ends] at hpath
  have hsum : ∀ es : List (ConcreteEdge d N),
      (es.map (fun e => ‖covariantEdgeDefect rho U phi e‖)).sum ≤
        (es.map (fun _e => ‖covariantD0CLM rho U phi‖)).sum := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
        simp only [List.map_cons, List.sum_cons]
        apply add_le_add
        · rw [norm_covariantEdgeDefect_eq]
          exact PiLp.norm_apply_le _ (physicalBondOfEdge e)
        · exact ih
  calc
    ‖phi GammaStart - rho.adCLM (Gamma.holonomy U) (phi GammaEnd)‖ ≤
        (Gamma.edges.map
          (fun e => ‖covariantEdgeDefect rho U phi e‖)).sum := hpath
    _ ≤ (Gamma.edges.map
          (fun _e => ‖covariantD0CLM rho U phi‖)).sum := hsum Gamma.edges
    _ = Gamma.edges.length * ‖covariantD0CLM rho U phi‖ := by
      simp

variable {M N' : ℕ} [NeZero M] [NeZero N']

/-- Every literal contour used by the one-scale source average is controlled
by the physical covariant derivative with the printed block-length cost. -/
theorem norm_cmp99BlockContainedContour_defect_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) :
    ‖phi (blockBasepoint M N' y) -
        rho.adCLM
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x)
          (phi x)‖ ≤
      (d * (M - 1) : ℕ) * ‖covariantD0CLM rho U phi‖ := by
  let Gamma := cmp99BlockContainedContourSystem (G := SUN Nc) y x
  have hpath := norm_covariantPathDefect_le_length_mul rho U phi Gamma
  have hlen : Gamma.edges.length ≤ d * (M - 1) :=
    cmp99BlockContainedContourSystem_length_le (G := SUN Nc) y x hx
  calc
    ‖phi (blockBasepoint M N' y) -
        rho.adCLM
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x)
          (phi x)‖ ≤
      Gamma.edges.length * ‖covariantD0CLM rho U phi‖ := hpath
    _ ≤ (d * (M - 1) : ℕ) * ‖covariantD0CLM rho U phi‖ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (norm_nonneg _)

end

end YangMills.RG
