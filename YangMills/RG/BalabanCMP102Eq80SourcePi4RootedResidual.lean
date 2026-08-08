/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4DomainEnumeration
import YangMills.RG.BalabanCMP116Eq229ConnectedDomainSum
import YangMills.RG.BalabanCMP116SourceCenteredPhysicalAEInteraction

/-!
# Direct equation-(80) rooted residual ledger

The selected equation-(80) domains already live on the terminal coarse
block graph.  Their rooted entropy therefore has no coarsification-fibre
factor.  This module derives the direct rooted equation-(2.20) ledger from
the generic connected-domain sum, the degree-eight four-dimensional face
graph, and the shifted source form of equation (2.30).

No rooted sum or cardinality bound is accepted as an input.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Exact reindexing of a filtered direct-domain sum from the canonical
`Fin` dictionary back to the selected physical labels. -/
theorem sum_cmp102Eq80SourcePi4DomainAt_filter_blocks_eq
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (root : FinBox 4 (2 * Q))
    (f : CMP102Eq80SourcePi4PhysicalDomainLabel anchor → ℝ) :
    (∑ i ∈ (Finset.univ.filter fun i :
          Fin (CMP102Eq80SourcePi4DomainCount anchor D) =>
        root ∈
          (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor D i).blocks),
        f (cmp102Eq80SourcePi4DomainAt anchor D i)) =
      ∑ W ∈ D.filter (fun W => root ∈ W.1), f W := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  conv_rhs =>
    rw [← image_cmp102Eq80SourcePi4DomainAt_univ anchor D]
  rw [Finset.sum_image
    (cmp102Eq80SourcePi4DomainAt_injective anchor D).injOn]
  rfl

/-- Rooted lattice-animal bound for the selected direct block domains.

There is no `M^4` factor: the direct carriers are already subsets of the
coarse `FinBox 4 (2 * Q)` graph. -/
theorem cmp102Eq80SourcePi4DomainFamily_rooted_sum_pow_card_le
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (root : FinBox 4 (2 * Q))
    (q : ℝ) (hq0 : 0 ≤ q) (hsmall : 64 * q < 1) :
    (∑ W ∈ D.filter (fun W => root ∈ W.1), q ^ W.1.card) ≤
      (1 - 64 * q)⁻¹ := by
  classical
  let relevant := D.filter fun W => root ∈ W.1
  let blockFamily : Finset (Finset (FinBox 4 (2 * Q))) :=
    D.image fun W => W.1
  have himage :
      relevant.image (fun W => W.1) =
        blockFamily.filter (fun blocks => root ∈ blocks) := by
    ext blocks
    constructor
    · intro hblocks
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hblocks
      have hWmem := Finset.mem_filter.mp hW
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨W, hWmem.1, rfl⟩, hWmem.2⟩
    · intro hblocks
      have hmem := Finset.mem_filter.mp hblocks
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hmem.1
      exact Finset.mem_image.mpr
        ⟨W, Finset.mem_filter.mpr ⟨hW, hmem.2⟩, rfl⟩
  have hdomains :
      ∀ blocks ∈ blockFamily,
        walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) blocks := by
    intro blocks hblocks
    obtain ⟨W, _hW, rfl⟩ := Finset.mem_image.mp hblocks
    exact (CMP102Eq80SourcePi4PhysicalDomainLabel.properties anchor W).2
  have hanimal :=
    connectedDomainFamily_rooted_sum_pow_card_le
      blockFamily root hdomains
      (Δ := 8) (q := q)
      (cmp116CoarseFaceAdj_degree_le_eight (2 * Q))
      (by norm_num) hq0 (by norm_num; exact hsmall)
  calc
    (∑ W ∈ D.filter (fun W => root ∈ W.1), q ^ W.1.card) =
        ∑ W ∈ relevant, q ^ W.1.card := by rfl
    _ = ∑ blocks ∈ relevant.image (fun W => W.1),
          q ^ blocks.card := by
      rw [Finset.sum_image Subtype.coe_injective.injOn]
    _ = ∑ blocks ∈ blockFamily.filter (fun blocks => root ∈ blocks),
          q ^ blocks.card := by rw [himage]
    _ ≤ (1 - 64 * q)⁻¹ := by
      norm_num at hanimal ⊢
      exact hanimal

/-- Equation (2.30) turns the direct tree metric into block-cardinality
decay with only the singleton factor `exp decay`. -/
theorem exp_neg_cmp102Eq80SourcePi4Metric_le_cardWeight
    {M Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor)
    (decay : ℝ) (hdecay : 0 ≤ decay) :
    Real.exp
        (-(decay *
          (cmp116CubeEdgeTreeMetric
            (cmp102Eq80SourcePi4LocalizationDomain
              (M := M) anchor W) : ℝ))) ≤
      Real.exp decay * Real.exp (-(decay / 24)) ^ W.1.card := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmetric :=
    cmp116LocalizationDomain_eq230_shifted
      (cmp102Eq80SourcePi4LocalizationDomain (M := M) anchor W)
  have hscaled :
      decay * ((W.1.card : ℝ) / 24) ≤
        decay *
          ((cmp116CubeEdgeTreeMetric
            (cmp102Eq80SourcePi4LocalizationDomain
              (M := M) anchor W) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hmetric hdecay
  nlinarith

/-- Uniform direct rooted sum of tree-metric exponentials. -/
theorem cmp102Eq80SourcePi4DomainFamily_rooted_exp_metric_sum_le
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (root : FinBox 4 (2 * Q))
    (decay : ℝ) (hdecay : 0 ≤ decay)
    (hsmall : 64 * Real.exp (-(decay / 24)) < 1) :
    (∑ W ∈ D.filter (fun W => root ∈ W.1),
        Real.exp
          (-(decay *
            (cmp116CubeEdgeTreeMetric
              (cmp102Eq80SourcePi4LocalizationDomain
                (M := M) anchor W) : ℝ)))) ≤
      Real.exp decay *
        (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by
  let q : ℝ := Real.exp (-(decay / 24))
  let relevant := D.filter fun W => root ∈ W.1
  have hpoint :
      ∀ W ∈ relevant,
        Real.exp
            (-(decay *
              (cmp116CubeEdgeTreeMetric
                (cmp102Eq80SourcePi4LocalizationDomain
                  (M := M) anchor W) : ℝ))) ≤
          Real.exp decay * q ^ W.1.card := by
    intro W _hW
    simpa [q] using
      exp_neg_cmp102Eq80SourcePi4Metric_le_cardWeight
        (M := M) anchor W decay hdecay
  have hcard :=
    cmp102Eq80SourcePi4DomainFamily_rooted_sum_pow_card_le
      anchor D root q (Real.exp_nonneg _)
        (by simpa [q] using hsmall)
  calc
    (∑ W ∈ D.filter (fun W => root ∈ W.1),
        Real.exp
          (-(decay *
            (cmp116CubeEdgeTreeMetric
              (cmp102Eq80SourcePi4LocalizationDomain
                (M := M) anchor W) : ℝ)))) =
        ∑ W ∈ relevant,
          Real.exp
            (-(decay *
              (cmp116CubeEdgeTreeMetric
                (cmp102Eq80SourcePi4LocalizationDomain
                  (M := M) anchor W) : ℝ))) := by rfl
    _ ≤ ∑ W ∈ relevant, Real.exp decay * q ^ W.1.card := by
      exact Finset.sum_le_sum fun W hW => hpoint W hW
    _ = Real.exp decay * (∑ W ∈ relevant, q ^ W.1.card) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp decay * (1 - 64 * q)⁻¹ :=
      mul_le_mul_of_nonneg_left hcard (Real.exp_nonneg _)
    _ = Real.exp decay *
        (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by rfl

/-- Amplitude-weighted direct rooted metric sum. -/
theorem cmp102Eq80SourcePi4DomainFamily_rooted_weighted_exp_metric_sum_le
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (root : FinBox 4 (2 * Q))
    (amplitude decay : ℝ)
    (hamplitude : 0 ≤ amplitude) (hdecay : 0 ≤ decay)
    (hsmall : 64 * Real.exp (-(decay / 24)) < 1) :
    (∑ W ∈ D.filter (fun W => root ∈ W.1),
        amplitude *
          Real.exp
            (-(decay *
              (cmp116CubeEdgeTreeMetric
                (cmp102Eq80SourcePi4LocalizationDomain
                  (M := M) anchor W) : ℝ)))) ≤
      amplitude * Real.exp decay *
        (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by
  have hsum :=
    cmp102Eq80SourcePi4DomainFamily_rooted_exp_metric_sum_le
      (M := M) anchor D root decay hdecay hsmall
  calc
    (∑ W ∈ D.filter (fun W => root ∈ W.1),
        amplitude *
          Real.exp
            (-(decay *
              (cmp116CubeEdgeTreeMetric
                (cmp102Eq80SourcePi4LocalizationDomain
                  (M := M) anchor W) : ℝ)))) =
        amplitude *
          (∑ W ∈ D.filter (fun W => root ∈ W.1),
            Real.exp
              (-(decay *
                (cmp116CubeEdgeTreeMetric
                  (cmp102Eq80SourcePi4LocalizationDomain
                    (M := M) anchor W) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ amplitude *
        (Real.exp decay *
          (1 - 64 * Real.exp (-(decay / 24)))⁻¹) :=
      mul_le_mul_of_nonneg_left hsum hamplitude
    _ = amplitude * Real.exp decay *
        (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by ring

/-- Explicit volume-uniform direct root bound. -/
noncomputable def cmp102Eq80SourcePi4DirectRootBound
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa alpha4 : ℝ) : ℝ :=
  let rate1 := (1 - 2 * delta) * kappa
  let rate2 := delta * kappa
  let amplitude :=
    E0 * epsilon1 * C1 * (M : ℝ) ^ q * Real.exp (C2 * kappa1)
  amplitude * Real.exp rate1 *
      (1 - 64 * Real.exp (-(rate1 / 24)))⁻¹ +
    alpha4 * Real.exp rate2 *
      (1 - 64 * Real.exp (-(rate2 / 24)))⁻¹

theorem cmp102Eq80SourcePi4DirectRootBound_nonneg
    {E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ}
    {M q : ℕ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hsmall1 :
      64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1) :
    0 ≤ cmp102Eq80SourcePi4DirectRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  have hden1 :
      0 < 1 - 64 *
        Real.exp (-(((1 - 2 * delta) * kappa) / 24)) :=
    sub_pos.mpr hsmall1
  have hden2 :
      0 < 1 - 64 * Real.exp (-((delta * kappa) / 24)) :=
    sub_pos.mpr hsmall2
  unfold cmp102Eq80SourcePi4DirectRootBound
  dsimp
  positivity

/-- The canonical direct enumeration satisfies the centered
equation-(2.20) rooted residual estimate. -/
theorem cmp102Eq80SourcePi4Indexed_rooted_residual_le
    {M Q q : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (root : FinBox 4 (2 * Q))
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hrate1 : 0 ≤ (1 - 2 * delta) * kappa)
    (hrate2 : 0 ≤ delta * kappa)
    (hsmall1 :
      64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1) :
    (∑ Y ∈ (Finset.univ.filter fun Y :
          Fin (CMP102Eq80SourcePi4DomainCount anchor D) =>
        root ∈
          (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor D Y).blocks),
      cmp116Eq220CenteredSourceResidualWeight
        (fun y =>
          (cmp102Eq80SourcePi4IndexedDomainMetricNat
            (M := M) anchor D y : ℝ))
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) ≤
      cmp102Eq80SourcePi4DirectRootBound
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  let rate1 := (1 - 2 * delta) * kappa
  let rate2 := delta * kappa
  let amplitude :=
    E0 * epsilon1 * C1 * (M : ℝ) ^ q * Real.exp (C2 * kappa1)
  have hamplitude : 0 ≤ amplitude := by
    dsimp [amplitude]
    positivity
  have hsum_eq :
      (∑ Y ∈ (Finset.univ.filter fun Y :
            Fin (CMP102Eq80SourcePi4DomainCount anchor D) =>
          root ∈
            (cmp102Eq80SourcePi4IndexedLocalizationDomain
              (M := M) anchor D Y).blocks),
        cmp116Eq220CenteredSourceResidualWeight
          (fun y =>
            (cmp102Eq80SourcePi4IndexedDomainMetricNat
              (M := M) anchor D y : ℝ))
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) =
        ∑ W ∈ D.filter (fun W => root ∈ W.1),
          (amplitude *
              Real.exp
                (-(rate1 *
                  (cmp116CubeEdgeTreeMetric
                    (cmp102Eq80SourcePi4LocalizationDomain
                      (M := M) anchor W) : ℝ))) +
            alpha4 *
              Real.exp
                (-(rate2 *
                  (cmp116CubeEdgeTreeMetric
                    (cmp102Eq80SourcePi4LocalizationDomain
                      (M := M) anchor W) : ℝ)))) := by
    simpa [cmp116Eq220CenteredSourceResidualWeight,
      cmp116Eq136ResidualMajorant,
      cmp116Eq220ResidualDomainWeight,
      cmp102Eq80SourcePi4IndexedDomainMetricNat,
      cmp102Eq80SourcePi4IndexedLocalizationDomain,
      amplitude, rate1, rate2, mul_assoc] using
      sum_cmp102Eq80SourcePi4DomainAt_filter_blocks_eq
        (M := M) anchor D root
          (fun W =>
            amplitude *
                Real.exp
                  (-(rate1 *
                    (cmp116CubeEdgeTreeMetric
                      (cmp102Eq80SourcePi4LocalizationDomain
                        (M := M) anchor W) : ℝ))) +
              alpha4 *
                Real.exp
                  (-(rate2 *
                    (cmp116CubeEdgeTreeMetric
                      (cmp102Eq80SourcePi4LocalizationDomain
                        (M := M) anchor W) : ℝ))))
  have hfirst :=
    cmp102Eq80SourcePi4DomainFamily_rooted_weighted_exp_metric_sum_le
      (M := M) anchor D root amplitude rate1 hamplitude
        (by simpa [rate1] using hrate1)
        (by simpa [rate1] using hsmall1)
  have hsecond :=
    cmp102Eq80SourcePi4DomainFamily_rooted_weighted_exp_metric_sum_le
      (M := M) anchor D root alpha4 rate2 halpha4
        (by simpa [rate2] using hrate2)
        (by simpa [rate2] using hsmall2)
  rw [hsum_eq, Finset.sum_add_distrib]
  calc
    (∑ W ∈ D.filter (fun W => root ∈ W.1),
        amplitude *
          Real.exp
            (-(rate1 *
              (cmp116CubeEdgeTreeMetric
                (cmp102Eq80SourcePi4LocalizationDomain
                  (M := M) anchor W) : ℝ)))) +
      ∑ W ∈ D.filter (fun W => root ∈ W.1),
        alpha4 *
          Real.exp
            (-(rate2 *
              (cmp116CubeEdgeTreeMetric
                (cmp102Eq80SourcePi4LocalizationDomain
                  (M := M) anchor W) : ℝ))) ≤
        amplitude * Real.exp rate1 *
            (1 - 64 * Real.exp (-(rate1 / 24)))⁻¹ +
          alpha4 * Real.exp rate2 *
            (1 - 64 * Real.exp (-(rate2 / 24)))⁻¹ :=
      add_le_add hfirst hsecond
    _ = cmp102Eq80SourcePi4DirectRootBound
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by rfl

end

end YangMills.RG
