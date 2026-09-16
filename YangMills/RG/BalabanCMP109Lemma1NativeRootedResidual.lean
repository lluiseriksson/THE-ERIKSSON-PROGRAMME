/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109Lemma1CoarsenedResidualFamily
import YangMills.RG.BalabanCMP116SourceCenteredPhysicalAEInteraction

/-!
# Native CMP109 Lemma-1 rooted residual ledger

This file discharges the rooted combinatorial sum generated when every
literal CMP109 Lemma-1 localization domain is retained as a distinct
equation-(2.26) index.  Only its physical support is coarsified.  Hence:

* no coarsification fiber is summed;
* the source tree metric remains the native one;
* the exact `M⁴` preimage cardinality of one coarse root is visible; and
* the only analytic conditions are the two explicit lattice-animal
  smallness inequalities for the two rates already present in the centered
  equation-(2.20) residual weight.

The result is stronger than the terminal `rooted_residual` field because it
holds for every coarse root, not merely roots in `Z₀`.  It does not prove
`domain_subset` or `volume_budget`.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Explicit volume-uniform bound for all native Lemma-1 domains whose
coarsified support contains one coarse root. -/
noncomputable def cmp109Lemma1NativeRootBound
    (E0 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa alpha4 : ℝ) : ℝ :=
  let rate1 := (1 - 2 * delta) * kappa
  let rate2 := delta * kappa
  let amplitude :=
    E0 * epsilon1 * C1 * (M : ℝ) ^ q * Real.exp (C2 * kappa1)
  amplitude * (M : ℝ) ^ 4 * Real.exp rate1 *
      (1 - 64 * Real.exp (-(rate1 / 24)))⁻¹ +
    alpha4 * (M : ℝ) ^ 4 * Real.exp rate2 *
      (1 - 64 * Real.exp (-(rate2 / 24)))⁻¹

/-- Positivity of the explicit native root bound follows from the same
scalar smallness conditions used in the animal sums. -/
theorem cmp109Lemma1NativeRootBound_nonneg
    {E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ}
    {M q : ℕ}
    (hE0 : 0 ≤ E0)
    (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1)
    (halpha4 : 0 ≤ alpha4)
    (hsmall1 :
      64 *
          Real.exp
            (-(((1 - 2 * delta) * kappa) / 24)) <
        1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1) :
    0 ≤
      cmp109Lemma1NativeRootBound
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
  have hden1 :
      0 <
        1 -
          64 *
            Real.exp
              (-(((1 - 2 * delta) * kappa) / 24)) :=
    sub_pos.mpr hsmall1
  have hden2 :
      0 < 1 - 64 * Real.exp (-((delta * kappa) / 24)) :=
    sub_pos.mpr hsmall2
  unfold cmp109Lemma1NativeRootBound
  dsimp
  positivity

/-- The canonical native enumeration satisfies the centered
equation-(2.20) rooted residual estimate.

Neither `rooted_residual` nor a prepackaged bound on this sum is a premise.
The two scalar smallness assumptions expose exactly the lattice-animal
entropy consumed by the two printed decay rates. -/
theorem cmp109Lemma1NativeIndexed_rooted_residual_le
    {Index : Type*} {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (root : FinBox 4 (2 * Q))
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ)
    (hE0 : 0 ≤ E0)
    (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1)
    (halpha4 : 0 ≤ alpha4)
    (hrate1 : 0 ≤ (1 - 2 * delta) * kappa)
    (hrate2 : 0 ≤ delta * kappa)
    (hsmall1 :
      64 *
          Real.exp
            (-(((1 - 2 * delta) * kappa) / 24)) <
        1)
    (hsmall2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1) :
    (∑ Y ∈ (Finset.univ.filter fun Y :
          Fin (CMP109Lemma1NativeDomainCount E) =>
        root ∈ cmp109Lemma1NativeIndexedDomainSupport E Y),
      cmp116Eq220CenteredSourceResidualWeight
        (fun y =>
          (cmp109Lemma1NativeIndexedDomainMetric E y : ℝ))
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) ≤
      cmp109Lemma1NativeRootBound
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
            Fin (CMP109Lemma1NativeDomainCount E) =>
          root ∈ cmp109Lemma1NativeIndexedDomainSupport E Y),
        cmp116Eq220CenteredSourceResidualWeight
          (fun y =>
            (cmp109Lemma1NativeIndexedDomainMetric E y : ℝ))
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 Y) =
        ∑ Y ∈
            ((cmp109Lemma1NativeDomainFamily E).filter fun Y =>
              root ∈ cmp109Lemma1CoarsenedBlocks Y),
          (amplitude *
                Real.exp
                  (-(rate1 *
                    (cmp116CubeEdgeTreeMetric Y : ℝ))) +
              alpha4 *
                Real.exp
                  (-(rate2 *
                    (cmp116CubeEdgeTreeMetric Y : ℝ)))) := by
    simpa [cmp116Eq220CenteredSourceResidualWeight,
      cmp116Eq136ResidualMajorant,
      cmp116Eq220ResidualDomainWeight,
      cmp109Lemma1NativeIndexedDomainMetric,
      amplitude, rate1, rate2, mul_assoc] using
      sum_cmp109Lemma1NativeDomainAt_filter_support_eq
        E root
          (fun Y =>
            amplitude *
                Real.exp
                  (-(rate1 *
                    (cmp116CubeEdgeTreeMetric Y : ℝ))) +
              alpha4 *
                Real.exp
                  (-(rate2 *
                    (cmp116CubeEdgeTreeMetric Y : ℝ))))
  have hfirst :=
    cmp109Lemma1NativeDomainFamily_coarsenedRoot_weighted_exp_metric_sum_le
      E root amplitude rate1 hamplitude
        (by simpa [rate1] using hrate1)
        (by simpa [rate1] using hsmall1)
  have hsecond :=
    cmp109Lemma1NativeDomainFamily_coarsenedRoot_weighted_exp_metric_sum_le
      E root alpha4 rate2 halpha4
        (by simpa [rate2] using hrate2)
        (by simpa [rate2] using hsmall2)
  rw [hsum_eq, Finset.sum_add_distrib]
  calc
    (∑ Y ∈
        ((cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y),
        amplitude *
          Real.exp
            (-(rate1 *
              (cmp116CubeEdgeTreeMetric Y : ℝ)))) +
      ∑ Y ∈
        ((cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y),
        alpha4 *
          Real.exp
            (-(rate2 *
              (cmp116CubeEdgeTreeMetric Y : ℝ))) ≤
        amplitude * (M : ℝ) ^ 4 * Real.exp rate1 *
            (1 - 64 * Real.exp (-(rate1 / 24)))⁻¹ +
          alpha4 * (M : ℝ) ^ 4 * Real.exp rate2 *
            (1 - 64 * Real.exp (-(rate2 / 24)))⁻¹ :=
      add_le_add hfirst hsecond
    _ =
        cmp109Lemma1NativeRootBound
          E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 := by
      rfl

end

end YangMills.RG
