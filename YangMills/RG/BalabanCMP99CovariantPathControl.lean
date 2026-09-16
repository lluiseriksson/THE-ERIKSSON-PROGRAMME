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
open scoped BigOperators

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

/-! ## Squared path energy localized to one source block -/

/-- The elementary Cauchy--Schwarz estimate for a finite list, exposed here
in the exact form used by path energies. -/
theorem list_sum_sq_le_length_mul_sum_sq (xs : List ℝ) :
    xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map (fun x => x ^ 2)).sum := by
  have h :=
    sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin xs.length)))
      (f := fun i : Fin xs.length => xs[i])
  simpa [Finset.card_univ, Fintype.card_fin,
    ← Fin.sum_univ_fun_getElem] using h

/-- Sum of squared physical covariant edge defects along a literal path. -/
noncomputable def covariantPathEnergy
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc)
    (es : List (ConcreteEdge d N)) : ℝ :=
  (es.map (fun e => ‖covariantEdgeDefect rho U phi e‖ ^ 2)).sum

/-- Squaring covariant telescoping costs exactly the path length times the
sum of squared edge defects. -/
theorem norm_covariantPathDefect_sq_le_length_mul_energy
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc)
    {GammaStart GammaEnd : FinBox d N}
    (Gamma : OrientedLatticePath (G := SUN Nc)
      (a := GammaStart) (b := GammaEnd)) :
    ‖phi GammaStart - rho.adCLM (Gamma.holonomy U) (phi GammaEnd)‖ ^ 2 ≤
      (Gamma.edges.length : ℝ) *
        covariantPathEnergy rho U phi Gamma.edges := by
  have hpath := norm_covariantPathDefect_le_sum rho U phi
    Gamma.edges GammaStart Gamma.isPath
  rw [Gamma.ends] at hpath
  have hnonneg :
      0 ≤ (Gamma.edges.map
        (fun e => ‖covariantEdgeDefect rho U phi e‖)).sum := by
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg _)
  have hsq :=
    (sq_le_sq₀ (norm_nonneg _)
      hnonneg).mpr hpath
  calc
    ‖phi GammaStart - rho.adCLM (Gamma.holonomy U) (phi GammaEnd)‖ ^ 2 ≤
        ((Gamma.edges.map
          (fun e => ‖covariantEdgeDefect rho U phi e‖)).sum) ^ 2 := hsq
    _ ≤ (Gamma.edges.length : ℝ) *
        ((Gamma.edges.map
          (fun e => ‖covariantEdgeDefect rho U phi e‖)).map
            (fun x => x ^ 2)).sum := by
      simpa using list_sum_sq_le_length_mul_sum_sq
        (Gamma.edges.map
          (fun e => ‖covariantEdgeDefect rho U phi e‖))
    _ = (Gamma.edges.length : ℝ) *
        covariantPathEnergy rho U phi Gamma.edges := by
      congr 1
      unfold covariantPathEnergy
      induction Gamma.edges with
      | nil => rfl
      | cons e es ih => simp only [List.map_cons, List.sum_cons, ih]

/-- Physical covariant derivative energy whose positive-bond source belongs
to the source block `y`. -/
noncomputable def cmp99BlockCovariantEnergy
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') : ℝ :=
  ∑ b : PhysicalBond d (M * N'),
    if b.1 ∈ blockOf M N' y then
      ‖covariantD0CLM rho U phi b‖ ^ 2
    else 0

theorem cmp99BlockCovariantEnergy_nonneg
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') :
    0 ≤ cmp99BlockCovariantEnergy rho U phi y := by
  unfold cmp99BlockCovariantEnergy
  exact Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

omit [NeZero Nc] in
/-- Any edge of a path staying in `y`'s block uses a positive-bond coordinate
whose source also belongs to that block. -/
theorem physicalBondOfEdge_fst_mem_blockOf_of_staysIn
    {a b : FinBox d (M * N')}
    {Gamma : OrientedLatticePath (G := SUN Nc) a b}
    {y : FinBox d N'}
    (hstay : Gamma.StaysIn (blockOf M N' y))
    {e : ConcreteEdge d (M * N')} (he : e ∈ Gamma.edges) :
    (physicalBondOfEdge e).1 ∈ blockOf M N' y := by
  have h := hstay e he
  cases e with
  | mk x i sign =>
      cases sign with
      | false => simpa [physicalBondOfEdge, ConcreteEdge.dstV] using h.2
      | true => simpa [physicalBondOfEdge, ConcreteEdge.srcV] using h.1

/-- Every squared edge defect on a block-contained path is bounded by the
entire covariant derivative energy of that same block. -/
theorem norm_covariantEdgeDefect_sq_le_blockEnergy_of_staysIn
    {a b : FinBox d (M * N')}
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    {Gamma : OrientedLatticePath (G := SUN Nc) a b}
    {y : FinBox d N'}
    (hstay : Gamma.StaysIn (blockOf M N' y))
    {e : ConcreteEdge d (M * N')} (he : e ∈ Gamma.edges) :
    ‖covariantEdgeDefect rho U phi e‖ ^ 2 ≤
      cmp99BlockCovariantEnergy rho U phi y := by
  rw [norm_covariantEdgeDefect_eq]
  unfold cmp99BlockCovariantEnergy
  have hmem := physicalBondOfEdge_fst_mem_blockOf_of_staysIn hstay he
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (PhysicalBond d (M * N'))))
    (f := fun b => if b.1 ∈ blockOf M N' y then
      ‖covariantD0CLM rho U phi b‖ ^ 2 else 0)
    (fun b _ => by dsimp; split_ifs <;> positivity)
    (Finset.mem_univ (physicalBondOfEdge e))
  simpa [hmem] using h

/-- The energy of a block-contained path is at most its length times the
energy of the source block.  Repeated edges require no separate simplicity
certificate. -/
theorem covariantPathEnergy_le_length_mul_blockEnergy_of_staysIn
    {a b : FinBox d (M * N')}
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    {Gamma : OrientedLatticePath (G := SUN Nc) a b}
    {y : FinBox d N'}
    (hstay : Gamma.StaysIn (blockOf M N' y)) :
    covariantPathEnergy rho U phi Gamma.edges ≤
      (Gamma.edges.length : ℝ) *
        cmp99BlockCovariantEnergy rho U phi y := by
  rw [covariantPathEnergy]
  calc
    (Gamma.edges.map
        (fun e => ‖covariantEdgeDefect rho U phi e‖ ^ 2)).sum ≤
        (Gamma.edges.map
          (fun _e => cmp99BlockCovariantEnergy rho U phi y)).sum := by
      apply List.sum_le_sum
      intro z hz
      exact norm_covariantEdgeDefect_sq_le_blockEnergy_of_staysIn
        rho U phi hstay hz
    _ = (Gamma.edges.length : ℝ) *
        cmp99BlockCovariantEnergy rho U phi y := by simp

/-- A literal one-scale source contour has squared endpoint defect bounded by
the square of the printed block length times the energy of its own block. -/
theorem norm_cmp99BlockContainedContour_defect_sq_le_blockEnergy
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' y) :
    ‖phi (blockBasepoint M N' y) -
        rho.adCLM
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x)
          (phi x)‖ ^ 2 ≤
      (d * (M - 1) : ℕ) ^ 2 *
        cmp99BlockCovariantEnergy rho U phi y := by
  let Gamma := cmp99BlockContainedContourSystem (G := SUN Nc) y x
  have hsq := norm_covariantPathDefect_sq_le_length_mul_energy
    rho U phi Gamma
  have henergy := covariantPathEnergy_le_length_mul_blockEnergy_of_staysIn
    rho U phi
      (cmp99BlockContainedContourSystem_staysIn
        (G := SUN Nc) y x hx)
  have hlen : (Gamma.edges.length : ℝ) ≤
      ((d * (M - 1) : ℕ) : ℝ) := by
    exact_mod_cast
      cmp99BlockContainedContourSystem_length_le (G := SUN Nc) y x hx
  have hblock := cmp99BlockCovariantEnergy_nonneg rho U phi y
  calc
    ‖phi (blockBasepoint M N' y) -
        rho.adCLM
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x)
          (phi x)‖ ^ 2 ≤
        (Gamma.edges.length : ℝ) *
          covariantPathEnergy rho U phi Gamma.edges := hsq
    _ ≤ (Gamma.edges.length : ℝ) ^ 2 *
        cmp99BlockCovariantEnergy rho U phi y := by
      calc
        (Gamma.edges.length : ℝ) *
            covariantPathEnergy rho U phi Gamma.edges ≤
          (Gamma.edges.length : ℝ) *
            ((Gamma.edges.length : ℝ) *
              cmp99BlockCovariantEnergy rho U phi y) := by
                exact mul_le_mul_of_nonneg_left henergy (by positivity)
        _ = (Gamma.edges.length : ℝ) ^ 2 *
            cmp99BlockCovariantEnergy rho U phi y := by ring
    _ ≤ (d * (M - 1) : ℕ) ^ 2 *
        cmp99BlockCovariantEnergy rho U phi y := by
      have hsqLen : (Gamma.edges.length : ℝ) ^ 2 ≤
          ((d * (M - 1) : ℕ) : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hsqLen hblock

/-- Summing all literal contour defects in one block costs only the fixed
block cardinality `M^d`, never the ambient volume. -/
theorem sum_norm_cmp99BlockContainedContour_defect_sq_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') :
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        ‖phi (blockBasepoint M N' y) -
          rho.adCLM
            (cmp99ContourHolonomy
              (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
            (phi x.1)‖ ^ 2 ≤
      (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp99BlockCovariantEnergy rho U phi y) := by
  calc
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        ‖phi (blockBasepoint M N' y) -
          rho.adCLM
            (cmp99ContourHolonomy
              (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
            (phi x.1)‖ ^ 2 ≤
      ∑ _x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
          cmp99BlockCovariantEnergy rho U phi y) := by
        apply Finset.sum_le_sum
        intro x _hx
        exact norm_cmp99BlockContainedContour_defect_sq_le_blockEnergy
          rho U phi y x.1 x.2
    _ = (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp99BlockCovariantEnergy rho U phi y) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        blockOf_card, nsmul_eq_mul]
      norm_cast

/-- The source blocks partition the physical covariant derivative energy
exactly. -/
theorem sum_cmp99BlockCovariantEnergy_eq_norm_sq
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc) :
    (∑ y : FinBox d N', cmp99BlockCovariantEnergy rho U phi y) =
      ‖covariantD0CLM rho U phi‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold cmp99BlockCovariantEnergy
  rw [Fintype.sum_prod_type]
  calc
    ∑ y : FinBox d N',
        (∑ b : FinBox d (M * N') × Fin d,
          if b.1 ∈ blockOf M N' y then
            ‖covariantD0CLM rho U phi b‖ ^ 2 else 0) =
      ∑ y : FinBox d N', ∑ x ∈ blockOf M N' y,
        ∑ i : Fin d, ‖covariantD0CLM rho U phi (x, i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [Fintype.sum_prod_type]
          calc
            ∑ x : FinBox d (M * N'), (∑ i : Fin d,
                if (x, i).1 ∈ blockOf M N' y then
                  ‖covariantD0CLM rho U phi (x, i)‖ ^ 2 else 0) =
              ∑ x : FinBox d (M * N'),
                (if x ∈ blockOf M N' y then
                  (∑ i : Fin d,
                    ‖covariantD0CLM rho U phi (x, i)‖ ^ 2) else 0) := by
                    apply Finset.sum_congr rfl
                    intro x _hx
                    by_cases hx : x ∈ blockOf M N' y <;> simp [hx]
            _ = ∑ x ∈ blockOf M N' y,
                ∑ i : Fin d,
                  ‖covariantD0CLM rho U phi (x, i)‖ ^ 2 := by
                    rw [← Finset.sum_filter]
                    simp [blockOf]
    _ = ∑ x : FinBox d (M * N'),
        ∑ i : Fin d, ‖covariantD0CLM rho U phi (x, i)‖ ^ 2 := by
          exact sum_blockOf M N'
            (fun x => ∑ i : Fin d,
              ‖covariantD0CLM rho U phi (x, i)‖ ^ 2)

end

end YangMills.RG
