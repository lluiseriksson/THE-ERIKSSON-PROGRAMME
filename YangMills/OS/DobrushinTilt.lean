/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinBridge
import YangMills.OS.DobrushinTransport
import YangMills.OS.SpatialGibbs

/-!
# D-6 corollary, stage A — the tilt layer: band covariances against the
free strip measure, exactly

Design: `docs/DOBRUSHIN-D6-B2-DESIGN.md` §§4-6 (the tilt identity, the
five-term formula, the denominator floor), realised as the first of two
files; gates G22-G23 measured every identity below to `1e-10` before any
Lean of this layer existed (ledger Addendum 597).

## What this module is

For a strictly positive slice weight `w`, coupling `β`, and Perron data
`(lam, Om)` for the symmetrised kernel, with the boundary tilt

    tilt = Om / √w        (the design note records that the fabricating
                           desk first wrote `Om·√w` in scratch — the
                           dressing-conflation failure mode of charter
                           Amendment 2, caught by the derivation and
                           measured by gate G22)

the band weight of B-1 for the NORMALISED kernel is EXACTLY the free
strip Gibbs weight of paper 9, tilted at the two end slices and scaled by
`lam^n` (`bandW_eq_tilt`); band two-endpoint sums, the band mass, and the
band marginals are `gibbsPathSum`s at tilted observables
(`band_sum_mul_pow`, `mass_mul_pow`, `marginal_left_mul_pow`,
`marginal_right_mul_pow`); and the band covariance satisfies the
DIVISION-FREE identity `bandCov_mul_sq`

    bandCov · PS(ψ,ψ)² = PS(fψ,gψ)·PS(ψ,ψ) − PS(fψ,ψ)·PS(ψ,gψ).

Stage A's endpoint `bandCov_decay_of_free_decay` turns uniform decay of
FREE two-endpoint covariances — the hypothesis the geometry bridge and
D-5 discharge in stage B — into decay of band covariances at the SAME
rate, the whole cost (sup norms, the floor `c ≤ ψ`, the shared constant
`D`) absorbed into the per-observable constant, exactly as the consumer's
quantifier order permits.

## What is deliberately NOT here

* NO geometry: nothing here mentions rectangles, `rectJ`, or the curry
  bijection; the free-decay hypothesis is stated on paper 9's strip sums
  and stage B discharges it.
* NO uniformity in the extent: everything is at one fixed `L`; constants
  may and do depend on `(L, f, g)` freely (B-2's binding non-goals).
* NO spectral input: `lam` enters only through the eigen-relation; no
  gap, no `specRatio`, no eigenvalue comparison.
* NO manufactured witness: this stage is the LEMMA of the corollary; its
  inhabitant is stage B's physical instantiation, and pretending a
  degenerate one-point witness certified anything would be exactly the
  vacuity theatre the house forbids.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## §1  The tilt and the normalised kernel as a matrix -/

/-- The boundary tilt `Ω/√w`: the exact factor by which the
Perron-boundary band measure differs from the free strip measure at the
two end slices. -/
noncomputable def tilt (w Om : (Fin L → Fin 2) → ℝ)
    (σ : Fin L → Fin 2) : ℝ :=
  Om σ / Real.sqrt (w σ)

theorem tilt_pos {w Om : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (hOm : ∀ σ, 0 < Om σ) (σ : Fin L → Fin 2) : 0 < tilt w Om σ :=
  div_pos (hOm σ) (Real.sqrt_pos.mpr (hw σ))

/-- The normalised symmetrised kernel, packaged as the matrix B-1
consumes. -/
noncomputable def tiltKernel (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ) :
    Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℝ :=
  Matrix.of fun σ τ => normalizedKernel (symWeighted w β) lam σ τ

theorem tiltKernel_apply (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ)
    (σ τ : Fin L → Fin 2) :
    tiltKernel w β lam σ τ = symWeighted w β σ τ / lam := rfl

theorem tiltKernel_symm (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ) :
    ∀ σ τ, tiltKernel w β lam σ τ = tiltKernel w β lam τ σ := by
  intro σ τ
  rw [tiltKernel_apply, tiltKernel_apply, symWeighted_symm]

/-! ## §2  The band weight is the tilted free weight -/

theorem prod_tiltKernel (w : (Fin L → Fin 2) → ℝ) (β lam : ℝ) (n : ℕ)
    (p : Fin (n + 1) → Fin L → Fin 2) :
    (∏ idx : Fin n, tiltKernel w β lam (p idx.castSucc) (p idx.succ))
      = (∏ idx : Fin n, symWeighted w β (p idx.castSucc) (p idx.succ))
          / lam ^ n := by
  rw [show (∏ idx : Fin n,
        tiltKernel w β lam (p idx.castSucc) (p idx.succ))
      = ∏ idx : Fin n,
          symWeighted w β (p idx.castSucc) (p idx.succ) / lam from
    Finset.prod_congr rfl fun idx _ => tiltKernel_apply w β lam _ _]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The tilt identity for the band weight** (design note §4, gate G22):
the band weight of the normalised kernel is the free strip Gibbs weight
with the tilt `Ω/√w` at both ends, over `lam^n`. -/
theorem bandW_eq_tilt {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (Om : (Fin L → Fin 2) → ℝ) (β : ℝ) {lam : ℝ} (hlam : 0 < lam) (n : ℕ)
    (p : Fin (n + 1) → Fin L → Fin 2) :
    bandW (tiltKernel w β lam) Om n p
      = tilt w Om (p 0) * gibbsWeight w β p * tilt w Om (p (Fin.last n))
          / lam ^ n := by
  unfold bandW
  rw [prod_tiltKernel, gibbsWeight_eq_dressed hw β p]
  unfold pathWeight tilt
  have h0 : Real.sqrt (w (p 0)) ≠ 0 :=
    (Real.sqrt_pos.mpr (hw (p 0))).ne'
  have hN : Real.sqrt (w (p (Fin.last n))) ≠ 0 :=
    (Real.sqrt_pos.mpr (hw (p (Fin.last n)))).ne'
  have hl : lam ^ n ≠ 0 := (pow_pos hlam n).ne'
  field_simp
  ring

/-- Band two-endpoint sums, multiplied through by `lam^n`: they are
`gibbsPathSum`s at the tilted observables. -/
theorem band_sum_mul_pow {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (Om : (Fin L → Fin 2) → ℝ) (β : ℝ) {lam : ℝ} (hlam : 0 < lam) (n : ℕ)
    (f g : (Fin L → Fin 2) → ℝ) :
    (∑ p : Fin (n + 1) → Fin L → Fin 2,
      f (p 0) * g (p (Fin.last n)) * bandW (tiltKernel w β lam) Om n p)
        * lam ^ n
      = gibbsPathSum w β n (fun σ => f σ * tilt w Om σ)
          (fun σ => g σ * tilt w Om σ) := by
  unfold gibbsPathSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bandW_eq_tilt hw Om β hlam n p,
    div_mul_eq_mul_div, mul_div_assoc,
    div_self (pow_pos hlam n).ne', mul_one]
  ring

/-! ## §3  Mass and marginals against the free sums -/

/-- The band mass: `(∑ Ω²) · lam^n = PS(ψ, ψ)`. -/
theorem mass_mul_pow {w Om : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (heig : ∀ σ, ∑ τ, tiltKernel w β lam σ τ * Om τ = Om σ) (n : ℕ) :
    (∑ σ, Om σ * Om σ) * lam ^ n
      = gibbsPathSum w β n (tilt w Om) (tilt w Om) := by
  have h2 := band_sum_mul_pow hw Om β hlam n
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  have h3 : (fun σ => (fun _ : Fin L → Fin 2 => (1 : ℝ)) σ * tilt w Om σ)
      = tilt w Om := funext fun σ => one_mul _
  rw [h3] at h2
  rw [← h2]
  have h1 : (∑ p : Fin (n + 1) → Fin L → Fin 2,
      (fun _ : Fin L → Fin 2 => (1 : ℝ)) (p 0)
        * (fun _ : Fin L → Fin 2 => (1 : ℝ)) (p (Fin.last n))
        * bandW (tiltKernel w β lam) Om n p)
      = ∑ p : Fin (n + 1) → Fin L → Fin 2,
          bandW (tiltKernel w β lam) Om n p :=
    Finset.sum_congr rfl fun p _ => by ring
  rw [h1, bandZ (tiltKernel w β lam) Om heig n]

/-- The left band marginal: `(∑ f·Ω²) · lam^n = PS(fψ, ψ)`. -/
theorem marginal_left_mul_pow {w Om : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (heig : ∀ σ, ∑ τ, tiltKernel w β lam σ τ * Om τ = Om σ)
    (f : (Fin L → Fin 2) → ℝ) (n : ℕ) :
    (∑ σ, f σ * Om σ * Om σ) * lam ^ n
      = gibbsPathSum w β n (fun σ => f σ * tilt w Om σ) (tilt w Om) := by
  have h5 := band_sum_mul_pow hw Om β hlam n f (fun _ => (1 : ℝ))
  have h3 : (fun σ => (fun _ : Fin L → Fin 2 => (1 : ℝ)) σ * tilt w Om σ)
      = tilt w Om := funext fun σ => one_mul _
  rw [h3] at h5
  rw [← h5]
  have hpair := band_pair (tiltKernel w β lam) Om n f (fun _ => (1 : ℝ))
  rw [hpair]
  have hin : ∀ i, (∑ j, (f i * Om i) * (tiltKernel w β lam ^ n) i j
      * ((fun _ : Fin L → Fin 2 => (1 : ℝ)) j * Om j))
      = f i * Om i * Om i := by
    intro i
    have h1 : ∀ j : Fin L → Fin 2,
        (f i * Om i) * (tiltKernel w β lam ^ n) i j
          * ((fun _ : Fin L → Fin 2 => (1 : ℝ)) j * Om j)
        = (f i * Om i) * ((tiltKernel w β lam ^ n) i j * Om j) := by
      intro j
      show (f i * Om i) * (tiltKernel w β lam ^ n) i j * (1 * Om j) = _
      ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.mul_sum,
      pow_fix (tiltKernel w β lam) Om heig n i]
  rw [Finset.sum_congr rfl fun i _ => hin i]

/-- The right band marginal: `(∑ g·Ω²) · lam^n = PS(ψ, gψ)`. -/
theorem marginal_right_mul_pow {w Om : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (heig : ∀ σ, ∑ τ, tiltKernel w β lam σ τ * Om τ = Om σ)
    (g : (Fin L → Fin 2) → ℝ) (n : ℕ) :
    (∑ σ, g σ * Om σ * Om σ) * lam ^ n
      = gibbsPathSum w β n (tilt w Om) (fun σ => g σ * tilt w Om σ) := by
  have h5 := band_sum_mul_pow hw Om β hlam n (fun _ => (1 : ℝ)) g
  have h3 : (fun σ => (fun _ : Fin L → Fin 2 => (1 : ℝ)) σ * tilt w Om σ)
      = tilt w Om := funext fun σ => one_mul _
  rw [h3] at h5
  rw [← h5]
  have hpair := band_pair (tiltKernel w β lam) Om n (fun _ => (1 : ℝ)) g
  rw [hpair]
  rw [Finset.sum_comm]
  have hin : ∀ j, (∑ i, ((fun _ : Fin L → Fin 2 => (1 : ℝ)) i * Om i)
      * (tiltKernel w β lam ^ n) i j * (g j * Om j))
      = g j * Om j * Om j := by
    intro j
    have h1 : ∀ i : Fin L → Fin 2,
        ((fun _ : Fin L → Fin 2 => (1 : ℝ)) i * Om i)
          * (tiltKernel w β lam ^ n) i j * (g j * Om j)
        = (Om i * (tiltKernel w β lam ^ n) i j) * (g j * Om j) := by
      intro i
      show (1 * Om i) * (tiltKernel w β lam ^ n) i j * (g j * Om j) = _
      ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.sum_mul,
      pow_fix_left (tiltKernel w β lam) Om (tiltKernel_symm w β lam)
        heig n j]
    ring
  rw [Finset.sum_congr rfl fun j _ => hin j]

/-! ## §4  The division-free covariance identity -/

/-- **The band covariance against free sums, with no division anywhere**
(design note §5, gate G22's five-term formula in its cleared form):

    bandCov · PS(ψ,ψ)² = PS(fψ,gψ)·PS(ψ,ψ) − PS(fψ,ψ)·PS(ψ,gψ). -/
theorem bandCov_mul_sq {w Om : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (hOm : ∀ σ, 0 < Om σ) (β : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (heig : ∀ σ, ∑ τ, tiltKernel w β lam σ τ * Om τ = Om σ)
    (f g : (Fin L → Fin 2) → ℝ) (n : ℕ) :
    bandCov (tiltKernel w β lam) Om n f g
        * gibbsPathSum w β n (tilt w Om) (tilt w Om) ^ 2
      = gibbsPathSum w β n (fun σ => f σ * tilt w Om σ)
            (fun σ => g σ * tilt w Om σ)
          * gibbsPathSum w β n (tilt w Om) (tilt w Om)
        - gibbsPathSum w β n (fun σ => f σ * tilt w Om σ) (tilt w Om)
          * gibbsPathSum w β n (tilt w Om)
              (fun σ => g σ * tilt w Om σ) := by
  have hS : 0 < ∑ σ, Om σ * Om σ := bandNorm_pos Om hOm
  have hS' : (∑ σ, Om σ * Om σ) ≠ 0 := hS.ne'
  rw [← mass_mul_pow hw β hlam heig n,
    ← band_sum_mul_pow hw Om β hlam n f g,
    ← marginal_left_mul_pow hw β hlam heig f n,
    ← marginal_right_mul_pow hw β hlam heig g n]
  unfold bandCov bandE
  field_simp
  ring

/-! ## §5  Sup bounds, the partition identity, positivity, and the floor -/

/-- The sup norm of a slice observable. -/
noncomputable def supObs (A : (Fin L → Fin 2) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun σ => |A σ|

theorem abs_le_supObs (A : (Fin L → Fin 2) → ℝ) (σ : Fin L → Fin 2) :
    |A σ| ≤ supObs A :=
  Finset.le_sup' _ (Finset.mem_univ σ)

theorem supObs_nonneg (A : (Fin L → Fin 2) → ℝ) : 0 ≤ supObs A :=
  le_trans (abs_nonneg (A fun _ => 0)) (abs_le_supObs A fun _ => 0)

/-- The partition function is the path sum at constant ends. -/
theorem gibbsPartition_eq_one_one (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (n : ℕ) :
    gibbsPartition w β n
      = gibbsPathSum w β n (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  unfold gibbsPartition gibbsPathSum
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The left marginal of the free measure is bounded by the sup norm. -/
theorem abs_PS_left_le {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) (n : ℕ) (A : (Fin L → Fin 2) → ℝ) :
    |gibbsPathSum w β n A (fun _ => (1 : ℝ))|
      ≤ supObs A * gibbsPartition w β n := by
  unfold gibbsPathSum
  calc |∑ p : Fin (n + 1) → Fin L → Fin 2,
        A (p 0) * (1 : ℝ) * gibbsWeight w β p|
      ≤ ∑ p : Fin (n + 1) → Fin L → Fin 2,
          |A (p 0) * (1 : ℝ) * gibbsWeight w β p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Fin (n + 1) → Fin L → Fin 2,
          supObs A * gibbsWeight w β p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [mul_one, abs_mul,
          abs_of_pos (gibbsWeight_pos hw β p)]
        exact mul_le_mul_of_nonneg_right (abs_le_supObs A (p 0))
          (gibbsWeight_pos hw β p).le
    _ = supObs A * gibbsPartition w β n := by
        rw [← Finset.mul_sum]
        rfl

/-- The right marginal of the free measure is bounded by the sup norm. -/
theorem abs_PS_right_le {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) (n : ℕ) (B : (Fin L → Fin 2) → ℝ) :
    |gibbsPathSum w β n (fun _ => (1 : ℝ)) B|
      ≤ supObs B * gibbsPartition w β n := by
  unfold gibbsPathSum
  calc |∑ p : Fin (n + 1) → Fin L → Fin 2,
        (1 : ℝ) * B (p (Fin.last n)) * gibbsWeight w β p|
      ≤ ∑ p : Fin (n + 1) → Fin L → Fin 2,
          |(1 : ℝ) * B (p (Fin.last n)) * gibbsWeight w β p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Fin (n + 1) → Fin L → Fin 2,
          supObs B * gibbsWeight w β p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [one_mul, abs_mul,
          abs_of_pos (gibbsWeight_pos hw β p)]
        exact mul_le_mul_of_nonneg_right
          (abs_le_supObs B (p (Fin.last n)))
          (gibbsWeight_pos hw β p).le
    _ = supObs B * gibbsPartition w β n := by
        rw [← Finset.mul_sum]
        rfl

/-- The tilted path sum is strictly positive. -/
theorem PS_tilt_pos {w Om : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (hOm : ∀ σ, 0 < Om σ) (β : ℝ) (n : ℕ) :
    0 < gibbsPathSum w β n (tilt w Om) (tilt w Om) := by
  unfold gibbsPathSum
  refine Finset.sum_pos (fun p _ => ?_) Finset.univ_nonempty
  exact mul_pos (mul_pos (tilt_pos hw hOm (p 0))
    (gibbsWeight_pos hw β p)) (tilt_pos hw hOm (p (Fin.last n)))

/-- **The denominator floor** (design note §6): a pointwise lower bound
`c ≤ ψ` forces `c²·Z ≤ PS(ψ,ψ)`, uniformly in the time horizon, with no
decay input. -/
theorem floor_PS_tilt {w Om : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (hOm : ∀ σ, 0 < Om σ) (β : ℝ) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hcle : ∀ σ, c ≤ tilt w Om σ) :
    c ^ 2 * gibbsPartition w β n
      ≤ gibbsPathSum w β n (tilt w Om) (tilt w Om) := by
  unfold gibbsPartition gibbsPathSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 : c ^ 2 ≤ tilt w Om (p 0) * tilt w Om (p (Fin.last n)) := by
    rw [pow_two]
    exact mul_le_mul (hcle (p 0)) (hcle (p (Fin.last n))) hc0
      (tilt_pos hw hOm (p 0)).le
  calc c ^ 2 * gibbsWeight w β p
      ≤ (tilt w Om (p 0) * tilt w Om (p (Fin.last n)))
          * gibbsWeight w β p :=
        mul_le_mul_of_nonneg_right h1 (gibbsWeight_pos hw β p).le
    _ = tilt w Om (p 0) * gibbsWeight w β p
          * tilt w Om (p (Fin.last n)) := by ring

/-! ## §6  The free expectation, the free covariance, and stage A's
endpoint -/

/-- The normalised free two-endpoint expectation. -/
noncomputable def freeE (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (n : ℕ)
    (A B : (Fin L → Fin 2) → ℝ) : ℝ :=
  gibbsPathSum w β n A B / gibbsPartition w β n

/-- The free two-endpoint covariance: the object stage B identifies with
D-5's rectangle covariance. -/
noncomputable def freeCov (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (n : ℕ)
    (A B : (Fin L → Fin 2) → ℝ) : ℝ :=
  freeE w β n A B
    - freeE w β n A (fun _ => (1 : ℝ)) * freeE w β n (fun _ => (1 : ℝ)) B

/-- **STAGE A's ENDPOINT** (design note §§5-6, gate G23's assembled
bound): if the free two-endpoint covariances of the strip decay at rate
`α` with per-observable constants `K·K·D`, then the band covariances of
the normalised kernel decay at the SAME rate, with a constant depending
on `(L, f, g)` only — never on `n`.  This is the entire boundary cost of
B-2, absorbed exactly where the consumer's quantifiers permit it. -/
theorem bandCov_decay_of_free_decay {w Om : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (hOm : ∀ σ, 0 < Om σ) (β : ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (heig : ∀ σ, ∑ τ, tiltKernel w β lam σ τ * Om τ = Om σ)
    {α D : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    {c : ℝ} (hc : 0 < c) (hcle : ∀ σ, c ≤ tilt w Om σ)
    (K : ((Fin L → Fin 2) → ℝ) → ℝ) (hK : ∀ A, 0 ≤ K A)
    (hfree : ∀ (n : ℕ) (A B : (Fin L → Fin 2) → ℝ),
      |freeCov w β n A B| ≤ K A * K B * D * α ^ n)
    (f g : (Fin L → Fin 2) → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |bandCov (tiltKernel w β lam) Om n f g| ≤ C * α ^ n := by
  set u : (Fin L → Fin 2) → ℝ := fun σ => f σ * tilt w Om σ with hu
  set v : (Fin L → Fin 2) → ℝ := fun σ => g σ * tilt w Om σ with hv
  set ψ : (Fin L → Fin 2) → ℝ := tilt w Om with hψ
  set Ku := K u
  set Kv := K v
  set Kp := K ψ
  set Mu := supObs u
  set Mv := supObs v
  set Mp := supObs ψ
  refine ⟨(Ku * Kv * D * (Kp * Kp * D)
      + Ku * Kv * D * (Mp * Mp)
      + Mu * Mv * (Kp * Kp * D)
      + Ku * Kp * D * (Kp * Kv * D)
      + Ku * Kp * D * (Mp * Mv)
      + Mu * Mp * (Kp * Kv * D)) / c ^ 4, ?_, ?_⟩
  · have hKu := hK u
    have hKv := hK v
    have hKp := hK ψ
    have hMu := supObs_nonneg u
    have hMv := supObs_nonneg v
    have hMp := supObs_nonneg ψ
    have hc4 : (0 : ℝ) < c ^ 4 := pow_pos hc 4
    positivity
  intro n
  have hZ : 0 < gibbsPartition w β n := gibbsPartition_pos hw β n
  have hPS : 0 < gibbsPathSum w β n ψ ψ := PS_tilt_pos hw hOm β n
  -- the E-level identity, obtained from the division-free one
  have hconv : ∀ A B : (Fin L → Fin 2) → ℝ,
      freeE w β n A B * gibbsPartition w β n
        = gibbsPathSum w β n A B := fun A B =>
    div_mul_cancel₀ _ hZ.ne'
  have hEpp : 0 < freeE w β n ψ ψ := div_pos hPS hZ
  have hE : bandCov (tiltKernel w β lam) Om n f g
      * freeE w β n ψ ψ ^ 2
      = freeE w β n u v * freeE w β n ψ ψ
        - freeE w β n u ψ * freeE w β n ψ v := by
    have hZ2 : gibbsPartition w β n ^ 2 ≠ 0 := pow_ne_zero 2 hZ.ne'
    apply mul_right_cancel₀ hZ2
    have hmain := bandCov_mul_sq hw hOm β hlam heig f g n
    calc bandCov (tiltKernel w β lam) Om n f g * freeE w β n ψ ψ ^ 2
          * gibbsPartition w β n ^ 2
        = bandCov (tiltKernel w β lam) Om n f g
            * (freeE w β n ψ ψ * gibbsPartition w β n) ^ 2 := by ring
      _ = bandCov (tiltKernel w β lam) Om n f g
            * gibbsPathSum w β n ψ ψ ^ 2 := by rw [hconv]
      _ = gibbsPathSum w β n u v * gibbsPathSum w β n ψ ψ
            - gibbsPathSum w β n u ψ * gibbsPathSum w β n ψ v := hmain
      _ = (freeE w β n u v * gibbsPartition w β n)
            * (freeE w β n ψ ψ * gibbsPartition w β n)
          - (freeE w β n u ψ * gibbsPartition w β n)
            * (freeE w β n ψ v * gibbsPartition w β n) := by
          rw [hconv, hconv, hconv, hconv]
      _ = (freeE w β n u v * freeE w β n ψ ψ
            - freeE w β n u ψ * freeE w β n ψ v)
            * gibbsPartition w β n ^ 2 := by ring
  -- the six-term expansion in free covariances
  have hnum : freeE w β n u v * freeE w β n ψ ψ
      - freeE w β n u ψ * freeE w β n ψ v
      = freeCov w β n u v * freeCov w β n ψ ψ
        + freeCov w β n u v
            * (freeE w β n ψ (fun _ => 1) * freeE w β n (fun _ => 1) ψ)
        + (freeE w β n u (fun _ => 1) * freeE w β n (fun _ => 1) v)
            * freeCov w β n ψ ψ
        - freeCov w β n u ψ * freeCov w β n ψ v
        - freeCov w β n u ψ
            * (freeE w β n ψ (fun _ => 1) * freeE w β n (fun _ => 1) v)
        - (freeE w β n u (fun _ => 1) * freeE w β n (fun _ => 1) ψ)
            * freeCov w β n ψ v := by
    unfold freeCov
    ring
  -- sup bounds on the free marginals
  have hmarg : ∀ A : (Fin L → Fin 2) → ℝ,
      |freeE w β n A (fun _ => 1)| ≤ supObs A := by
    intro A
    rw [show freeE w β n A (fun _ => 1)
        = gibbsPathSum w β n A (fun _ => 1) / gibbsPartition w β n
        from rfl, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    exact abs_PS_left_le hw β n A
  have hmarg' : ∀ B : (Fin L → Fin 2) → ℝ,
      |freeE w β n (fun _ => 1) B| ≤ supObs B := by
    intro B
    rw [show freeE w β n (fun _ => 1) B
        = gibbsPathSum w β n (fun _ => 1) B / gibbsPartition w β n
        from rfl, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    exact abs_PS_right_le hw β n B
  -- the floor at the E level
  have hfloor : c ^ 2 ≤ freeE w β n ψ ψ := by
    rw [show freeE w β n ψ ψ
        = gibbsPathSum w β n ψ ψ / gibbsPartition w β n from rfl,
      le_div_iff₀ hZ]
    exact floor_PS_tilt hw hOm β n hc.le hcle
  -- powers of alpha
  have han : (0 : ℝ) ≤ α ^ n := pow_nonneg hα0 n
  have han1 : α ^ n ≤ 1 := pow_le_one₀ hα0 hα1
  -- the six absolute bounds
  have hb1 : |freeCov w β n u v| * |freeCov w β n ψ ψ|
      ≤ Ku * Kv * D * (Kp * Kp * D) * α ^ n := by
    calc |freeCov w β n u v| * |freeCov w β n ψ ψ|
        ≤ (Ku * Kv * D * α ^ n) * (Kp * Kp * D * α ^ n) :=
          mul_le_mul (hfree n u v) (hfree n ψ ψ) (abs_nonneg _)
            (by positivity)
      _ = (Ku * Kv * D * (Kp * Kp * D)) * (α ^ n * α ^ n) := by ring
      _ ≤ (Ku * Kv * D * (Kp * Kp * D)) * (α ^ n * 1) := by
          have hKu := hK u; have hKv := hK v; have hKp := hK ψ
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left han1 han) (by positivity)
      _ = Ku * Kv * D * (Kp * Kp * D) * α ^ n := by ring
  have hb2 : |freeCov w β n u v|
        * (|freeE w β n ψ (fun _ => 1)| * |freeE w β n (fun _ => 1) ψ|)
      ≤ Ku * Kv * D * (Mp * Mp) * α ^ n := by
    calc |freeCov w β n u v|
          * (|freeE w β n ψ (fun _ => 1)| * |freeE w β n (fun _ => 1) ψ|)
        ≤ (Ku * Kv * D * α ^ n) * (Mp * Mp) := by
          refine mul_le_mul (hfree n u v) ?_ (by positivity) (by positivity)
          exact mul_le_mul (hmarg ψ) (hmarg' ψ) (abs_nonneg _)
            (supObs_nonneg ψ)
      _ = Ku * Kv * D * (Mp * Mp) * α ^ n := by ring
  have hb3 : (|freeE w β n u (fun _ => 1)| * |freeE w β n (fun _ => 1) v|)
        * |freeCov w β n ψ ψ|
      ≤ Mu * Mv * (Kp * Kp * D) * α ^ n := by
    calc (|freeE w β n u (fun _ => 1)| * |freeE w β n (fun _ => 1) v|)
          * |freeCov w β n ψ ψ|
        ≤ (Mu * Mv) * (Kp * Kp * D * α ^ n) := by
          refine mul_le_mul ?_ (hfree n ψ ψ) (abs_nonneg _) (by positivity)
          exact mul_le_mul (hmarg u) (hmarg' v) (abs_nonneg _)
            (supObs_nonneg u)
      _ = Mu * Mv * (Kp * Kp * D) * α ^ n := by ring
  have hb4 : |freeCov w β n u ψ| * |freeCov w β n ψ v|
      ≤ Ku * Kp * D * (Kp * Kv * D) * α ^ n := by
    calc |freeCov w β n u ψ| * |freeCov w β n ψ v|
        ≤ (Ku * Kp * D * α ^ n) * (Kp * Kv * D * α ^ n) :=
          mul_le_mul (hfree n u ψ) (hfree n ψ v) (abs_nonneg _)
            (by positivity)
      _ = (Ku * Kp * D * (Kp * Kv * D)) * (α ^ n * α ^ n) := by ring
      _ ≤ (Ku * Kp * D * (Kp * Kv * D)) * (α ^ n * 1) := by
          have hKu := hK u; have hKv := hK v; have hKp := hK ψ
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left han1 han) (by positivity)
      _ = Ku * Kp * D * (Kp * Kv * D) * α ^ n := by ring
  have hb5 : |freeCov w β n u ψ|
        * (|freeE w β n ψ (fun _ => 1)| * |freeE w β n (fun _ => 1) v|)
      ≤ Ku * Kp * D * (Mp * Mv) * α ^ n := by
    calc |freeCov w β n u ψ|
          * (|freeE w β n ψ (fun _ => 1)| * |freeE w β n (fun _ => 1) v|)
        ≤ (Ku * Kp * D * α ^ n) * (Mp * Mv) := by
          refine mul_le_mul (hfree n u ψ) ?_ (by positivity) (by positivity)
          exact mul_le_mul (hmarg ψ) (hmarg' v) (abs_nonneg _)
            (supObs_nonneg ψ)
      _ = Ku * Kp * D * (Mp * Mv) * α ^ n := by ring
  have hb6 : (|freeE w β n u (fun _ => 1)| * |freeE w β n (fun _ => 1) ψ|)
        * |freeCov w β n ψ v|
      ≤ Mu * Mp * (Kp * Kv * D) * α ^ n := by
    calc (|freeE w β n u (fun _ => 1)| * |freeE w β n (fun _ => 1) ψ|)
          * |freeCov w β n ψ v|
        ≤ (Mu * Mp) * (Kp * Kv * D * α ^ n) := by
          refine mul_le_mul ?_ (hfree n ψ v) (abs_nonneg _) (by positivity)
          exact mul_le_mul (hmarg u) (hmarg' ψ) (abs_nonneg _)
            (supObs_nonneg u)
      _ = Mu * Mp * (Kp * Kv * D) * α ^ n := by ring
  -- assemble
  have hEppne : freeE w β n ψ ψ ^ 2 ≠ 0 := by positivity
  have hband : bandCov (tiltKernel w β lam) Om n f g
      = (freeE w β n u v * freeE w β n ψ ψ
          - freeE w β n u ψ * freeE w β n ψ v)
        / freeE w β n ψ ψ ^ 2 := by
    rw [eq_div_iff hEppne]
    exact hE
  have habs6 : ∀ a b c' d e f' : ℝ,
      |a + b + c' - d - e - f'| ≤ |a| + |b| + |c'| + |d| + |e| + |f'| := by
    intro a b c' d e f'
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le a
      have h2 := neg_abs_le b
      have h3 := neg_abs_le c'
      have h4 := le_abs_self d
      have h5 := le_abs_self e
      have h6 := le_abs_self f'
      linarith
    · have h1 := le_abs_self a
      have h2 := le_abs_self b
      have h3 := le_abs_self c'
      have h4 := neg_abs_le d
      have h5 := neg_abs_le e
      have h6 := neg_abs_le f'
      linarith
  have habs : |bandCov (tiltKernel w β lam) Om n f g|
      ≤ (Ku * Kv * D * (Kp * Kp * D)
          + Ku * Kv * D * (Mp * Mp)
          + Mu * Mv * (Kp * Kp * D)
          + Ku * Kp * D * (Kp * Kv * D)
          + Ku * Kp * D * (Mp * Mv)
          + Mu * Mp * (Kp * Kv * D)) * α ^ n
        / freeE w β n ψ ψ ^ 2 := by
    rw [hband, abs_div, abs_of_nonneg (sq_nonneg (freeE w β n ψ ψ))]
    have hEpp2 : (0 : ℝ) < freeE w β n ψ ψ ^ 2 := pow_pos hEpp 2
    refine div_le_div_of_nonneg_right ?_ hEpp2.le
    calc |freeE w β n u v * freeE w β n ψ ψ
          - freeE w β n u ψ * freeE w β n ψ v|
        = |freeCov w β n u v * freeCov w β n ψ ψ
            + freeCov w β n u v
                * (freeE w β n ψ (fun _ => 1)
                    * freeE w β n (fun _ => 1) ψ)
            + (freeE w β n u (fun _ => 1) * freeE w β n (fun _ => 1) v)
                * freeCov w β n ψ ψ
            - freeCov w β n u ψ * freeCov w β n ψ v
            - freeCov w β n u ψ
                * (freeE w β n ψ (fun _ => 1)
                    * freeE w β n (fun _ => 1) v)
            - (freeE w β n u (fun _ => 1) * freeE w β n (fun _ => 1) ψ)
                * freeCov w β n ψ v| := by rw [hnum]
      _ ≤ |freeCov w β n u v * freeCov w β n ψ ψ|
            + |freeCov w β n u v
                * (freeE w β n ψ (fun _ => 1)
                    * freeE w β n (fun _ => 1) ψ)|
            + |(freeE w β n u (fun _ => 1) * freeE w β n (fun _ => 1) v)
                * freeCov w β n ψ ψ|
            + |freeCov w β n u ψ * freeCov w β n ψ v|
            + |freeCov w β n u ψ
                * (freeE w β n ψ (fun _ => 1)
                    * freeE w β n (fun _ => 1) v)|
            + |(freeE w β n u (fun _ => 1) * freeE w β n (fun _ => 1) ψ)
                * freeCov w β n ψ v| := habs6 _ _ _ _ _ _
      _ ≤ Ku * Kv * D * (Kp * Kp * D) * α ^ n
            + Ku * Kv * D * (Mp * Mp) * α ^ n
            + Mu * Mv * (Kp * Kp * D) * α ^ n
            + Ku * Kp * D * (Kp * Kv * D) * α ^ n
            + Ku * Kp * D * (Mp * Mv) * α ^ n
            + Mu * Mp * (Kp * Kv * D) * α ^ n := by
          simp only [abs_mul]
          exact add_le_add (add_le_add (add_le_add (add_le_add
            (add_le_add hb1 hb2) hb3) hb4) hb5) hb6
      _ = _ := by ring
  refine le_trans habs ?_
  have hc4 : (0 : ℝ) < c ^ 4 := pow_pos hc 4
  have hEc : c ^ 4 ≤ freeE w β n ψ ψ ^ 2 := by
    have h1 : (c ^ 2) ^ 2 ≤ freeE w β n ψ ψ ^ 2 := by
      have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
      exact pow_le_pow_left₀ hc2 hfloor 2
    calc c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ ≤ _ := h1
  have hnumnn : (0 : ℝ) ≤ (Ku * Kv * D * (Kp * Kp * D)
      + Ku * Kv * D * (Mp * Mp)
      + Mu * Mv * (Kp * Kp * D)
      + Ku * Kp * D * (Kp * Kv * D)
      + Ku * Kp * D * (Mp * Mv)
      + Mu * Mp * (Kp * Kv * D)) * α ^ n := by
    have hKu := hK u; have hKv := hK v; have hKp := hK ψ
    have hMu := supObs_nonneg u; have hMv := supObs_nonneg v
    have hMp := supObs_nonneg ψ
    positivity
  calc (Ku * Kv * D * (Kp * Kp * D)
        + Ku * Kv * D * (Mp * Mp)
        + Mu * Mv * (Kp * Kp * D)
        + Ku * Kp * D * (Kp * Kv * D)
        + Ku * Kp * D * (Mp * Mv)
        + Mu * Mp * (Kp * Kv * D)) * α ^ n
        / freeE w β n ψ ψ ^ 2
      ≤ (Ku * Kv * D * (Kp * Kp * D)
        + Ku * Kv * D * (Mp * Mp)
        + Mu * Mv * (Kp * Kp * D)
        + Ku * Kp * D * (Kp * Kv * D)
        + Ku * Kp * D * (Mp * Mv)
        + Mu * Mp * (Kp * Kv * D)) * α ^ n / c ^ 4 :=
        div_le_div_of_nonneg_left hnumnn hc4 hEc
    _ = (Ku * Kv * D * (Kp * Kp * D)
        + Ku * Kv * D * (Mp * Mp)
        + Mu * Mv * (Kp * Kp * D)
        + Ku * Kp * D * (Kp * Kv * D)
        + Ku * Kp * D * (Mp * Mv)
        + Mu * Mp * (Kp * Kv * D)) / c ^ 4 * α ^ n := by ring

end Dobrushin

end YangMills.OS
