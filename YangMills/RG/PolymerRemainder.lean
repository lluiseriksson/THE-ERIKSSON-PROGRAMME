/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.CouplingFlow

/-!
# The polymer cluster-sum bound (gauge-RG, UV `hpoly` summation step)

`docs/BALABAN-SOURCE-BOUNDS.md` §5.  The remainder `R_k` of Bałaban's RG
step is a sum of renormalized polymer activities `H_k(Y)` over the
boundary-touching polymers.  Dimock's cluster-expansion-with-holes
theorem supplies two estimates: an **activity decay bound**
`|H_k(Y)| ≤ (amplitude_k)·w(Y)` (the `H₀·e^{−(κ−3κ₀−3)d(Y)}` conclusion)
and a **geometric summability bound** `∑_Y w(Y) ≤ K₀` (the
`∑_{X⊇□} e^{−κ₀ d_M(X, mod Ω^c)} ≤ K₀` substrate).

This file proves the **summation step** that consumes those two
estimates to produce the `hpoly` input of `coupling_flow_bridge`:
`|R_k| = |∑_Y H_k(Y)| ≤ amplitude_k · K₀`.  This is a genuine analytic
step (absolute summability + termwise comparison), not a restatement.

**Honest scope (per the iron rules).**  The two estimates `hact` and
`hwK` are carried as **explicit hypotheses**, NOT axioms or `sorry` —
exactly Dimock's two outputs.  Proving them for the actual non-abelian
construction (the cluster expansion with holes itself) is the
months-scale analytic core that Mathlib has no primitives for; it is
**not** done here, and this file does not claim it.  This brick proves
the *summation* that turns those estimates into the remainder bound,
shrinking the frontier by that one step and isolating the rest precisely.
The cluster-expansion constants (`κ`, `κ₀`, the `3κ₀+3` offset) are kept
as **parameters** inside the weight `w` and the constant `K₀`, NOT
hard-coded, since their verbatim values (Dimock II Appendix F vs the
convergence in Dimock III, arXiv:1304.0705) must be read off the page,
not reconstructed.

**Source.** Dimock I/II/III (arXiv:1108.1335 / 1212.5562 / 1304.0705);
Bałaban CMP 122-II.  Strategy/framing: Lluis Eriksson
(ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open scoped BigOperators

/-- **Polymer cluster-sum bound** (the `hpoly` summation step): if the
scale-`k` remainder is the sum of renormalized activities
`R_k = ∑_Y H_k(Y)` (absolutely summable), each bounded by the amplitude
`A·g_k^{κ₀}` times a weight `w(Y)`, and the weights are summable with
`∑_Y w(Y) ≤ K₀`, then `|R_k| ≤ (A·K₀)·g_k^{κ₀}` — exactly the polymer
bound consumed by `coupling_flow_bridge`.  The two hypotheses `hact`
(activity decay) and `hwK` (geometric summability) are Dimock's two
cluster-expansion-with-holes estimates, carried explicitly. -/
theorem polymer_remainder_bound {ι : Type*} {κ₀ A K₀ : ℝ}
    (R : ℕ → ℝ) (H : ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ k, R k = ∑' Y, H k Y)
    (hHsummable : ∀ k, Summable (fun Y => |H k Y|))
    (hact : ∀ k Y, |H k Y| ≤ A * g k ^ κ₀ * w Y)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    ∀ k, |R k| ≤ A * K₀ * g k ^ κ₀ := by
  intro k
  have hamp : 0 ≤ A * g k ^ κ₀ := mul_nonneg hA (Real.rpow_nonneg (hg k) κ₀)
  have hsummRHS : Summable (fun Y => A * g k ^ κ₀ * w Y) := hwsum.mul_left _
  calc |R k| = |∑' Y, H k Y| := by rw [hR k]
    _ ≤ ∑' Y, |H k Y| := by
        have hs : Summable (fun Y => ‖H k Y‖) := by
          simpa [Real.norm_eq_abs] using hHsummable k
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs
    _ ≤ ∑' Y, A * g k ^ κ₀ * w Y :=
        (hHsummable k).tsum_le_tsum (fun Y => hact k Y) hsummRHS
    _ = A * g k ^ κ₀ * ∑' Y, w Y := tsum_mul_left
    _ ≤ A * g k ^ κ₀ * K₀ := mul_le_mul_of_nonneg_left hwK hamp
    _ = A * K₀ * g k ^ κ₀ := by ring

/-- **Assembled conditional remainder bound** (the full UV chain, modulo
the two genuinely-analytic inputs): given the cluster-expansion-with-holes
estimates (`hact`, `hwK`) AND the irrelevant coupling recursion
(`hrec`, `hb`), the remainder decays geometrically,
`|R_k| ≤ (A·K₀·g_0^{κ₀})·r^k`.  Composition of `polymer_remainder_bound`
(→ the `hpoly` bound) and `remainder_geometric_of_logistic`
(`hg`-discharge + bridge).  Everything is oracle-clean; the only
unproved content is the two carried estimates (`hact`/`hwK`, the cluster
expansion) and the coupling recursion (`hrec`) — sharply isolated. -/
theorem geometric_remainder_assembled {ι : Type*} {κ₀ A K₀ r β : ℝ}
    (R : ℕ → ℝ) (H : ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    (hA : 0 ≤ A) (hK₀ : 0 ≤ K₀) (hr0 : 0 < r) (hr1 : r ≤ 1) (hκ : 1 ≤ κ₀)
    (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ k, R k = ∑' Y, H k Y)
    (hHsummable : ∀ k, Summable (fun Y => |H k Y|))
    (hact : ∀ k Y, |H k Y| ≤ A * g k ^ κ₀ * w Y)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀)
    (hb : ∀ k, 0 ≤ β * g k ∧ β * g k ≤ 1)
    (hrec : ∀ k, g (k + 1) ≤ r * g k * (1 - β * g k)) :
    ∀ k, |R k| ≤ A * K₀ * g 0 ^ κ₀ * r ^ k := by
  have hpoly := polymer_remainder_bound R H w g hA hg hR hHsummable hact hwsum hwK
  exact remainder_geometric_of_logistic g R (mul_nonneg hA hK₀) hr0 hr1 hκ hg hb hrec hpoly

/-- **Geometric summability core** (the convergence substrate of `hwK`):
if the per-size polymer count `c_n` is bounded by the animal bound `Cⁿ`
and the per-size decay factor `q` satisfies the Kotecký–Preiss-style
smallness `C·q < 1`, then the size-graded weight sum converges,
`∑_n c_n·qⁿ ≤ (1 − C·q)⁻¹`.  This is exactly the geometric criterion
behind Dimock's `∑_{X⊇□} e^{−κ₀ d(X)} ≤ K₀` (with `q = e^{−κ₀}`,
`K₀ = (1−Cq)⁻¹`): it reduces the cluster-expansion summability `hwK` to
the **polymer animal-counting bound** `c_n ≤ Cⁿ` — pure lattice
combinatorics, the one remaining elementary input on this branch.
Termwise comparison with the geometric series. -/
theorem geometric_size_summability (c : ℕ → ℝ) {C q : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hcC : ∀ n, c n ≤ C ^ n) (hq : 0 ≤ q)
    (hC : 0 ≤ C) (hCq : C * q < 1) :
    ∑' n, c n * q ^ n ≤ (1 - C * q)⁻¹ := by
  have hCq0 : 0 ≤ C * q := mul_nonneg hC hq
  have hgeo : Summable (fun n => (C * q) ^ n) :=
    summable_geometric_of_lt_one hCq0 hCq
  have hterm : ∀ n, c n * q ^ n ≤ (C * q) ^ n := by
    intro n
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hcC n) (pow_nonneg hq n)
  have hsumm : Summable (fun n => c n * q ^ n) :=
    hgeo.of_nonneg_of_le (fun n => mul_nonneg (hc n) (pow_nonneg hq n)) hterm
  calc ∑' n, c n * q ^ n ≤ ∑' n, (C * q) ^ n := hsumm.tsum_le_tsum hterm hgeo
    _ = (1 - C * q)⁻¹ := tsum_geometric_of_lt_one hCq0 hCq

/-- **Polymer-indexed geometric summability** (reduces `hwK` to the
animal count): polymers `Y` graded by `size : ι → ℕ` with finite per-size
fibers whose count obeys the animal bound `#{size = n} ≤ Cⁿ`, and per-size
decay `q` with `C·q < 1`, give `∑_Y q^{size Y} ≤ (1 − C·q)⁻¹`.  This is the
cluster-expansion summability `hwK` (`q = e^{−κ₀}`, `K₀ = (1−Cq)⁻¹`)
**reduced to the polymer animal-counting bound** `c_n ≤ Cⁿ` — pure lattice
combinatorics, the last elementary input on the summability branch.
Fiber decomposition (`Equiv.sigmaFiberEquiv`, `Summable.tsum_sigma`) onto
`geometric_size_summability`. -/
theorem polymer_weight_summability {ι : Type*} (size : ι → ℕ)
    [∀ n, Fintype {Y : ι // size Y = n}] {C q : ℝ}
    (hq0 : 0 ≤ q) (hC0 : 0 ≤ C) (hCq : C * q < 1)
    (hcount : ∀ n, (Fintype.card {Y : ι // size Y = n} : ℝ) ≤ C ^ n)
    (hsumm : Summable (fun Y : ι => q ^ size Y)) :
    ∑' Y : ι, q ^ size Y ≤ (1 - C * q)⁻¹ := by
  have hsig : Summable
      (fun p : Σ n, {Y : ι // size Y = n} =>
        q ^ size ((Equiv.sigmaFiberEquiv size) p)) :=
    ((Equiv.sigmaFiberEquiv size).summable_iff).mpr hsumm
  have hval : ∀ (n : ℕ) (b : {Y : ι // size Y = n}),
      q ^ size ((Equiv.sigmaFiberEquiv size) ⟨n, b⟩) = q ^ n := by
    intro n b
    show q ^ size (b : ι) = q ^ n
    rw [b.2]
  calc ∑' Y : ι, q ^ size Y
      = ∑' p : Σ n, {Y : ι // size Y = n},
          q ^ size ((Equiv.sigmaFiberEquiv size) p) :=
        ((Equiv.sigmaFiberEquiv size).tsum_eq (fun Y => q ^ size Y)).symm
    _ = ∑' n : ℕ, ∑' b : {Y : ι // size Y = n},
          q ^ size ((Equiv.sigmaFiberEquiv size) ⟨n, b⟩) := hsig.tsum_sigma
    _ = ∑' n : ℕ, (Fintype.card {Y : ι // size Y = n} : ℝ) * q ^ n := by
        refine tsum_congr (fun n => ?_)
        rw [tsum_congr (fun b => hval n b), tsum_fintype, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
    _ ≤ (1 - C * q)⁻¹ :=
        geometric_size_summability _ (fun _ => by positivity) hcount hq0 hC0 hCq

end YangMills.RG
