/-
Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Kotecky-Preiss Smallness Criterion

The Kotecky-Preiss (KP) criterion for convergence of the polymer cluster
expansion. Given polymer activities with geometric decay $|\rho(X)| \le A_0 \cdot r^{\mathrm{diam}(X)}$
and $r \in (0, 1)$, we set the KP parameter $a := -\log(r)/2$ and show
that the KP-weighted activity $r \cdot e^{a}$ is strictly less than one.
This ensures the KP-weighted polymer sum $\sum_n C_{\mathrm{anim}} n^d A_0 (r e^{a})^n$
converges, which is the analytic input for the cluster-expansion convergence
(Theorem 5.3 of [Eriksson Feb 2026], §5.3.2).

Reference: Kotecký-Preiss, CMP 1986; [Eriksson Feb 2026] §5.3.2.
-/

import Mathlib
import YangMills.ClayCore.OscillationBound

namespace YangMills

/-! ## The KP parameter -/

/-- The KP parameter associated with geometric decay rate $r \in (0, 1)$:
$a := -\log(r)/2$. This is half the log-decay rate, chosen so that the
KP-weighted activity $r \cdot e^{a}$ satisfies $r \cdot e^{a} = \sqrt{r} < 1$. -/
noncomputable def kpParameter (r : ℝ) : ℝ := -Real.log r / 2

/-- The KP parameter is strictly positive whenever $r \in (0, 1)$. -/
theorem kpParameter_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < kpParameter r := by
  unfold kpParameter
  have hlogr : Real.log r < 0 := Real.log_neg hr hr1
  linarith

/-! ## The KP-weighted decay rate -/

/-- **KP decay identity**: for $r \in (0, 1)$ and $a = -\log(r)/2$,
$r \cdot e^{a} = e^{\log(r)/2} < 1$. Equivalently, $r \cdot e^{a} = \sqrt{r}$. -/
theorem kp_decay_rate_lt_one {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r * Real.exp (kpParameter r) < 1 := by
  unfold kpParameter
  have hlogr : Real.log r < 0 := Real.log_neg hr hr1
  calc r * Real.exp (-Real.log r / 2)
      = Real.exp (Real.log r) * Real.exp (-Real.log r / 2) := by
          rw [Real.exp_log hr]
    _ = Real.exp (Real.log r + -Real.log r / 2) := by rw [← Real.exp_add]
    _ = Real.exp (Real.log r / 2) := by congr 1; ring
    _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-! ## Summability of the KP-weighted polymer sum -/

/-- The KP-weighted polymer sum $\sum_n C_{\mathrm{anim}} n^d A_0 (r e^{a})^n$
is summable whenever $r \cdot e^{a} < 1$. -/
theorem kp_sum_summable
    (pab : PolymerActivityBound)
    (a : ℝ) (hrate : pab.r * Real.exp a < 1) :
    Summable (fun n : ℕ => pab.C_anim * ((n : ℝ)) ^ pab.dim * pab.A₀ *
        (pab.r * Real.exp a) ^ n) := by
  have h_rxp_nn : 0 ≤ pab.r * Real.exp a :=
    mul_nonneg pab.hr_pos.le (Real.exp_pos _).le
  have h_norm : ‖pab.r * Real.exp a‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg h_rxp_nn]
    exact hrate
  have hsum_basic : Summable
      (fun n : ℕ => ((n : ℝ)) ^ pab.dim * (pab.r * Real.exp a) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one pab.dim h_norm
  have hmul := hsum_basic.mul_left (pab.C_anim * pab.A₀)
  have heq :
      (fun n : ℕ => pab.C_anim * pab.A₀ *
          (((n : ℝ)) ^ pab.dim * (pab.r * Real.exp a) ^ n))
      = (fun n : ℕ => pab.C_anim * ((n : ℝ)) ^ pab.dim * pab.A₀ *
          (pab.r * Real.exp a) ^ n) := by
    funext n; ring
  rw [heq] at hmul
  exact hmul

/-! ## Main KP smallness theorem -/

/-- **Main KP result (terminal KP criterion)**: Given a polymer activity bound
with geometric decay parameter $r \in (0, 1)$, there is a strictly positive
KP parameter $a = -\log(r)/2$ for which the KP-weighted polymer sum
$\sum_n C_{\mathrm{anim}} \cdot n^d \cdot A_0 \cdot (r e^{a})^n$ converges.
This is the analytic input for convergence of the cluster expansion of the
terminal remainder $R^*$. -/
theorem terminal_kp_criterion (pab : PolymerActivityBound) :
    ∃ a : ℝ, 0 < a ∧
      Summable (fun n : ℕ => pab.C_anim * ((n : ℝ)) ^ pab.dim * pab.A₀ *
          (pab.r * Real.exp a) ^ n) := by
  refine ⟨kpParameter pab.r, kpParameter_pos pab.hr_pos pab.hr_lt_one, ?_⟩
  exact kp_sum_summable pab (kpParameter pab.r)
    (kp_decay_rate_lt_one pab.hr_pos pab.hr_lt_one)

end YangMills
