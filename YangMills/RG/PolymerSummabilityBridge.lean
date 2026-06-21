/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PolymerClusterWithHolesBridge

/-!
# Residual polymer summability bridge

This module isolates the downstream bookkeeping behind a with-holes cluster
expansion estimate.  The source theorem is represented only by the pointwise
residual bound in `ClusterExpansionWithHolesEstimate`; the analytic proof of
that estimate remains outside this file.

There are two honest summability routes:

* if geometric summability is available at the residual rate
  `κ - 3κ₀ - 3`, then the aggregate bound follows at that residual rate; and
* if one wants to reuse a geometric estimate stated at exponent `κ₀`, then
  Lean requires the stronger comparison hypothesis
  `κ₀ ≤ κ - 3κ₀ - 3`, supplied for instance by `κ ≥ 4κ₀ + 3`.

Thus the usual condition `κ ≥ 3κ₀ + 3` is recorded only as residual
nonnegativity; by itself it does not justify comparison with the `κ₀`
geometric weight.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Source-facing interface for a with-holes cluster-expansion estimate after
the Appendix-F losses have been paid.  It packages only the pointwise residual
bound; summability is supplied separately so that the residual-rate and
reference-`κ₀` routes cannot be confused. -/
structure ClusterExpansionWithHolesEstimate {ι : Type*}
    (Hsharp : ι → ℝ) (metric : ι → ℕ)
    (C H₀ κ κ₀ : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  H0_nonneg : 0 ≤ H₀
  pointwise_bound : ∀ Y,
    |Hsharp Y| ≤ C * H₀ *
      Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ)))

namespace ClusterExpansionWithHolesEstimate

variable {ι : Type*} {Hsharp : ι → ℝ} {metric : ι → ℕ}
variable {C H₀ K κ κ₀ : ℝ}

/-- The standard margin `κ ≥ 3κ₀ + 3` proves only that the residual exponent is
nonnegative. -/
theorem residualRate_nonneg_of_three_mul_add_le
    (hκ : 3 * κ₀ + 3 ≤ κ) :
    0 ≤ polymerClusterResidualRate κ κ₀ :=
  polymerClusterResidualRate_nonneg_of_three_mul_add_le hκ

/-- Finite downstream summation at the residual exponent.  This is the local
bookkeeping used before taking any infinite sum. -/
theorem finite_sum_abs_le_residualWeightSum
    (hE : ClusterExpansionWithHolesEstimate Hsharp metric C H₀ κ κ₀)
    (s : Finset ι) :
    (∑ Y ∈ s, |Hsharp Y|) ≤
      C * H₀ *
        ∑ Y ∈ s,
          Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))) := by
  classical
  calc
    (∑ Y ∈ s, |Hsharp Y|)
        ≤ ∑ Y ∈ s,
            C * H₀ *
              Real.exp
                (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))) :=
          Finset.sum_le_sum fun Y _hY => hE.pointwise_bound Y
    _ =
        C * H₀ *
          ∑ Y ∈ s,
            Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))) := by
          rw [Finset.mul_sum]

/-- Infinite downstream summation when the geometric theorem is stated at the
residual exponent itself. -/
theorem abs_tsum_le_of_residual_summability
    (hE : ClusterExpansionWithHolesEstimate Hsharp metric C H₀ κ κ₀)
    (hgeom :
      Summable fun Y =>
        Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))))
    (hgeomK :
      (∑' Y,
        Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ)))) ≤ K) :
    Summable (fun Y => |Hsharp Y|) ∧
      (∑' Y, |Hsharp Y|) ≤ C * H₀ * K := by
  classical
  let w : ι → ℝ := fun Y =>
    Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ)))
  have hAmp : 0 ≤ C * H₀ := mul_nonneg hE.C_nonneg hE.H0_nonneg
  have hmajor : Summable (fun Y => C * H₀ * w Y) :=
    hgeom.mul_left _
  have habs : Summable (fun Y => |Hsharp Y|) :=
    hmajor.of_nonneg_of_le (fun Y => abs_nonneg (Hsharp Y))
      (fun Y => by simpa [w] using hE.pointwise_bound Y)
  refine ⟨habs, ?_⟩
  calc
    (∑' Y, |Hsharp Y|) ≤ ∑' Y, C * H₀ * w Y :=
      habs.tsum_le_tsum
        (fun Y => by simpa [w] using hE.pointwise_bound Y) hmajor
    _ = C * H₀ * ∑' Y, w Y := tsum_mul_left
    _ ≤ C * H₀ * K := mul_le_mul_of_nonneg_left (by simpa [w] using hgeomK) hAmp

/-- Combined diagnostic route: `κ ≥ 3κ₀ + 3` gives nonnegative residual rate,
and residual-rate summability then gives the aggregate bound. -/
theorem residualRate_nonneg_and_abs_tsum_le_of_residual_summability
    (hE : ClusterExpansionWithHolesEstimate Hsharp metric C H₀ κ κ₀)
    (hκ : 3 * κ₀ + 3 ≤ κ)
    (hgeom :
      Summable fun Y =>
        Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))))
    (hgeomK :
      (∑' Y,
        Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ)))) ≤ K) :
    0 ≤ polymerClusterResidualRate κ κ₀ ∧
      Summable (fun Y => |Hsharp Y|) ∧
        (∑' Y, |Hsharp Y|) ≤ C * H₀ * K := by
  exact ⟨residualRate_nonneg_of_three_mul_add_le hκ,
    hE.abs_tsum_le_of_residual_summability hgeom hgeomK⟩

/-- Infinite downstream summation when reusing a geometric theorem stated at
the reference exponent `κ₀`.  The comparison hypothesis
`κ₀ ≤ κ - 3κ₀ - 3` is explicit. -/
theorem abs_tsum_le_of_reference_summability
    (hE : ClusterExpansionWithHolesEstimate Hsharp metric C H₀ κ κ₀)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hgeom : Summable fun Y => Real.exp (-(κ₀ * (metric Y : ℝ))))
    (hgeomK :
      (∑' Y, Real.exp (-(κ₀ * (metric Y : ℝ)))) ≤ K) :
    Summable (fun Y => |Hsharp Y|) ∧
      (∑' Y, |Hsharp Y|) ≤ C * H₀ * K :=
  polymerClusterWithHoles_abs_tsum_le Hsharp metric hE.C_nonneg
    hE.H0_nonneg hres hE.pointwise_bound hgeom hgeomK

/-- Reference-exponent route with the explicit sufficient margin
`κ ≥ 4κ₀ + 3`. -/
theorem abs_tsum_le_of_reference_summability_four_mul_margin
    (hE : ClusterExpansionWithHolesEstimate Hsharp metric C H₀ κ κ₀)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hgeom : Summable fun Y => Real.exp (-(κ₀ * (metric Y : ℝ))))
    (hgeomK :
      (∑' Y, Real.exp (-(κ₀ * (metric Y : ℝ)))) ≤ K) :
    Summable (fun Y => |Hsharp Y|) ∧
      (∑' Y, |Hsharp Y|) ≤ C * H₀ * K :=
  hE.abs_tsum_le_of_reference_summability
    (kappa0_le_polymerClusterResidualRate_of_four_mul_add_le hκ)
    hgeom hgeomK

end ClusterExpansionWithHolesEstimate

end YangMills.RG
