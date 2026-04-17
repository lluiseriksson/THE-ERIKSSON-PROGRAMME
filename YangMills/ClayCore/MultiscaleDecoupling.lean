/-
Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Multiscale Correlator Decoupling (Section 6).
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.GCongr
import YangMills.ClayCore.ExponentialClustering

namespace YangMills

open Real

/-! ## 6.1 Telescoping Identity -/

structure RGScaleData (k_star : Nat) where
  L : Nat
  hL : 2 ≤ L
  eta : Real
  heta : 0 < eta
  a : Nat -> Real
  ha_def : ∀ k, a k = (L : Real)^k * eta
  corr : Nat -> Real
  corr_terminal : Real

theorem rg_spacing_geometric {k_star : Nat} (rg : RGScaleData k_star) (k : Nat) :
    rg.a (k + 1) = (rg.L : Real) * rg.a k := by
  rw [rg.ha_def, rg.ha_def, pow_succ]
  ring

theorem rg_inv_spacing_geometric {k_star : Nat} (rg : RGScaleData k_star) (k : Nat) :
    1 / rg.a (k + 1) = (1 / (rg.L : Real)) * (1 / rg.a k) := by
  rw [rg_spacing_geometric]
  have hL_pos : (0 : Real) < (rg.L : Real) := by
    have h2 : (2 : Real) ≤ (rg.L : Real) := by exact_mod_cast rg.hL
    linarith
  have hak_pos : (0 : Real) < rg.a k := by
    rw [rg.ha_def]
    exact mul_pos (pow_pos hL_pos k) rg.heta
  have hLne : (rg.L : Real) ≠ 0 := ne_of_gt hL_pos
  have hakne : rg.a k ≠ 0 := ne_of_gt hak_pos
  field_simp

theorem telescoping_identity {k_star : Nat} (rg : RGScaleData k_star) :
    rg.corr 0 - rg.corr_terminal =
    (Finset.sum (Finset.range k_star) (fun k => rg.corr k - rg.corr (k + 1))) +
    (rg.corr k_star - rg.corr_terminal) := by
  have aux : ∀ n : Nat, rg.corr 0 - rg.corr n =
      Finset.sum (Finset.range n) (fun k => rg.corr k - rg.corr (k + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring
  linarith [aux k_star]

/-! ## 6.2 Single-Scale UV Bound -/

structure UVBoundData (k_star : Nat) (dist_phys : Real) where
  kappa : Real
  hkappa : 0 < kappa
  C_UV : Real
  hC_UV : 0 < C_UV
  rg : RGScaleData k_star
  h_single_scale : ∀ k, k < k_star ->
    |rg.corr k - rg.corr (k + 1)| ≤
    C_UV * Real.exp (-kappa * dist_phys / rg.a k)

structure TerminalBound where
  C_clust : Real
  hC_clust : 0 < C_clust
  r : Real
  hr_pos : 0 < r
  hr_lt_one : r < 1

theorem uv_scale_sum_bound {k_star : Nat} {dist_phys : Real}
    (uvb : UVBoundData k_star dist_phys) :
    Finset.sum (Finset.range k_star)
      (fun k => |uvb.rg.corr k - uvb.rg.corr (k + 1)|) ≤
    Finset.sum (Finset.range k_star)
      (fun k => uvb.C_UV * Real.exp (-uvb.kappa * dist_phys / uvb.rg.a k)) := by
  apply Finset.sum_le_sum
  intro k hk
  exact uvb.h_single_scale k (Finset.mem_range.mp hk)

/-! ## 6.3 Multiscale Assembly -/

/-- Local triangle inequality: avoids name/import ambiguity on abs_add. -/
private theorem abs_add_real (x y : Real) : |x + y| ≤ |x| + |y| := by
  have h1 : x + y ≤ |x| + |y| := by linarith [le_abs_self x, le_abs_self y]
  have hnegx : -x ≤ |x| := by rw [← abs_neg]; exact le_abs_self (-x)
  have hnegy : -y ≤ |y| := by rw [← abs_neg]; exact le_abs_self (-y)
  have h2 : -(|x| + |y|) ≤ x + y := by linarith
  exact abs_le.mpr ⟨h2, h1⟩

theorem multiscale_correlator_bound
    {k_star : Nat} {dist_phys : Real} {dist_lat : Nat}
    (uvb : UVBoundData k_star dist_phys)
    (tb : TerminalBound)
    (h_terminal : |uvb.rg.corr k_star - uvb.rg.corr_terminal| ≤
      tb.C_clust * tb.r ^ dist_lat) :
    |uvb.rg.corr 0 - uvb.rg.corr_terminal| ≤
    Finset.sum (Finset.range k_star)
      (fun k => uvb.C_UV * Real.exp (-uvb.kappa * dist_phys / uvb.rg.a k)) +
    tb.C_clust * tb.r ^ dist_lat := by
  have htele := telescoping_identity uvb.rg
  have habs : |uvb.rg.corr 0 - uvb.rg.corr_terminal| ≤
      |Finset.sum (Finset.range k_star)
        (fun k => uvb.rg.corr k - uvb.rg.corr (k + 1))| +
      |uvb.rg.corr k_star - uvb.rg.corr_terminal| := by
    rw [htele]
    exact abs_add_real _ _
  calc |uvb.rg.corr 0 - uvb.rg.corr_terminal|
      ≤ |Finset.sum (Finset.range k_star)
            (fun k => uvb.rg.corr k - uvb.rg.corr (k + 1))| +
          |uvb.rg.corr k_star - uvb.rg.corr_terminal| := habs
    _ ≤ Finset.sum (Finset.range k_star)
            (fun k => |uvb.rg.corr k - uvb.rg.corr (k + 1)|) +
          |uvb.rg.corr k_star - uvb.rg.corr_terminal| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (Finset.range k_star)
            (fun k => uvb.C_UV * Real.exp (-uvb.kappa * dist_phys / uvb.rg.a k)) +
          tb.C_clust * tb.r ^ dist_lat :=
        add_le_add (uv_scale_sum_bound uvb) h_terminal

/-! ## Assembly: Mass Gap Bound -/

theorem pow_eq_exp_log_mul {r : Real} (hr : 0 < r) (n : Nat) :
    r ^ n = Real.exp ((n : Real) * Real.log r) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    have hcast : ((m + 1 : Nat) : Real) = (m : Real) + 1 := by push_cast; ring
    rw [hcast]
    rw [show ((m : Real) + 1) * Real.log r = (m : Real) * Real.log r + Real.log r from by ring]
    rw [Real.exp_add, Real.exp_log hr]

theorem mass_gap_bound
    {k_star : Nat} {dist_phys : Real} {dist_lat : Nat}
    (uvb : UVBoundData k_star dist_phys)
    (tb : TerminalBound)
    (h_terminal : |uvb.rg.corr k_star - uvb.rg.corr_terminal| ≤
      tb.C_clust * tb.r ^ dist_lat) :
    ∃ m : Real, 0 < m ∧ ∃ C_total : Real, 0 ≤ C_total ∧
    |uvb.rg.corr 0 - uvb.rg.corr_terminal| ≤
    Finset.sum (Finset.range k_star)
      (fun k => uvb.C_UV * Real.exp (-uvb.kappa * dist_phys / uvb.rg.a k)) +
    C_total * Real.exp (-m * (dist_lat : Real)) := by
  refine ⟨-Real.log tb.r, ?_, tb.C_clust, le_of_lt tb.hC_clust, ?_⟩
  · have hneg : Real.log tb.r < 0 := Real.log_neg tb.hr_pos tb.hr_lt_one
    linarith
  · have hbound := multiscale_correlator_bound uvb tb h_terminal
    have hr_exp : tb.r ^ dist_lat =
        Real.exp (-(-Real.log tb.r) * (dist_lat : Real)) := by
      rw [neg_neg, pow_eq_exp_log_mul tb.hr_pos dist_lat]
      congr 1; ring
    rw [← hr_exp]
    exact hbound

end YangMills