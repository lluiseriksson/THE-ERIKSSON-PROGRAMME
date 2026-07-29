/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3i: Perron--Frobenius for strictly positive kernels, and the coupled vacuum at
EVERY spatial extent.

Charter: docs/O-BRIDGE-CHARTER.md.
-/

import Mathlib
import YangMills.OS.SpatialPerron

/-!
# O-3i — Perron--Frobenius for positive kernels, and the vacuum at every `L`

## Why this module exists

Twice the absence of a Perron--Frobenius theorem from the pinned `mathlib` has
forced a detour: O-3f had to declare the vacuum unavailable, and O-3h had to
prove its domination bound from scratch.  A dependency that bites twice is
structural, so it is discharged here.

## What is proved, for a strictly positive kernel `A` on a finite nonempty type

* `exists_pos_eigenvector` — a strictly positive eigenvector exists, with a
  strictly positive eigenvalue.  **By compactness, not by a fixed-point
  theorem**: the library has no Brouwer.  The pair `(r, x)` is maximised in `r`
  over the compact set cut out by `r x ≤ A x` on the simplex; maximality forces
  equality, since a strict inequality anywhere would let one more application of
  `A` produce an admissible pair with a larger `r`.  The bound that keeps the
  set compact is obtained by *summing the constraint*: `r = r ∑ x ≤ ∑ (A x)`.
* `pos_eigenvector_unique` — any two strictly positive eigenvectors are
  proportional, and their eigenvalues agree.
* `eigenvector_eq_smul_of_pos` — *geometric simplicity*: every real eigenvector
  for that eigenvalue is a scalar multiple of the positive one.
* the eigenvalue is the spectral radius, by the domination theorems of O-3h,
  which were already stated for a general kernel.

## The application

`sourceWeightedKernelL` is the decoupled kernel of O-3f times **any** strictly
positive weight on the source configuration, at **any** spatial extent.  The
coupled kernel of O-3f is one instance and `coupledKernelL` (a bond around the
slice) is another.  For all of them, at every `L`, a strictly positive
eigenvector exists, is unique up to scale, and its eigenvalue dominates every
eigenvalue, real or complex.

That is exactly the object O-3f showed the elementary route stops producing.  It
was never absent; it was unavailable *to that route*.

## What is NOT claimed

Algebraic simplicity of the eigenvalue (only the geometric statement is proved);
Perron--Frobenius for merely irreducible kernels; periodicity; and **no spectral
gap of any kind**, uniform in the volume or otherwise.  A gap is a different
problem and this module does not touch it.

Nothing here concerns `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

section PositiveKernel

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ### §1  Elementary consequences of strict positivity -/

/-- A strictly positive kernel sends a nonnegative, somewhere-positive vector to
a strictly positive one. -/
theorem apply_pos_of_nonneg {A : ι → ι → ℝ} (hA : ∀ i j, 0 < A i j)
    {z : ι → ℝ} (hz : ∀ j, 0 ≤ z j) {j₀ : ι} (hj₀ : 0 < z j₀) (i : ι) :
    0 < ∑ j, A i j * z j := by
  have hterm : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ A i j * z j := fun j _ =>
    mul_nonneg (le_of_lt (hA i j)) (hz j)
  calc (0:ℝ) < A i j₀ * z j₀ := mul_pos (hA i j₀) hj₀
    _ ≤ ∑ j, A i j * z j := Finset.single_le_sum hterm (Finset.mem_univ j₀)

/-- The eigenvalue of a strictly positive eigenvector is strictly positive. -/
theorem eigenvalue_pos {A : ι → ι → ℝ} (hA : ∀ i j, 0 < A i j)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, A i j * v j = lam * v i) : 0 < lam := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h1 : 0 < ∑ j, A i₀ j * v j :=
    apply_pos_of_nonneg hA (fun j => le_of_lt (hv j)) (hv i₀) i₀
  rw [hvE i₀] at h1
  nlinarith [h1, hv i₀]

/-! ### §2  Uniqueness up to scale, and geometric simplicity -/

/-- If `A z = lam • z` with `z` nonnegative and vanishing somewhere, then `z`
vanishes identically.  This one comparison carries both statements below. -/
theorem eq_zero_of_nonneg_of_eigen_of_zero {A : ι → ι → ℝ} (hA : ∀ i j, 0 < A i j)
    {z : ι → ℝ} (hz : ∀ j, 0 ≤ z j) {lam : ℝ}
    (hzE : ∀ i, ∑ j, A i j * z j = lam * z i) {i₀ : ι} (hi₀ : z i₀ = 0) :
    ∀ j, z j = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨j₀, hj₀⟩ := hcon
  have hpos : 0 < z j₀ := lt_of_le_of_ne (hz j₀) (Ne.symm hj₀)
  have h1 : 0 < ∑ j, A i₀ j * z j := apply_pos_of_nonneg hA hz hpos i₀
  rw [hzE i₀, hi₀, mul_zero] at h1
  exact lt_irrefl 0 h1

/-- **Geometric simplicity.** -/
theorem eigenvector_eq_smul_of_pos {A : ι → ι → ℝ} (hA : ∀ i j, 0 < A i j)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, A i j * v j = lam * v i)
    {w : ι → ℝ} (hwE : ∀ i, ∑ j, A i j * w j = lam * w i) :
    ∃ c : ℝ, ∀ i, w i = c * v i := by
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ (fun i => w i / v i)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  refine ⟨w i₀ / v i₀, ?_⟩
  have hz : ∀ j, 0 ≤ w j - w i₀ / v i₀ * v j := by
    intro j
    have hle := hmin j (Finset.mem_univ _)
    have hmul : w i₀ / v i₀ * v j ≤ w j := (le_div_iff₀ (hv j)).mp hle
    linarith
  have hzE : ∀ i, ∑ j, A i j * (w j - w i₀ / v i₀ * v j)
      = lam * (w i - w i₀ / v i₀ * v i) := by
    intro i
    calc ∑ j, A i j * (w j - w i₀ / v i₀ * v j)
        = ∑ j, (A i j * w j - w i₀ / v i₀ * (A i j * v j)) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j, A i j * w j) - ∑ j, w i₀ / v i₀ * (A i j * v j) :=
          Finset.sum_sub_distrib _ _
      _ = (∑ j, A i j * w j) - w i₀ / v i₀ * ∑ j, A i j * v j := by
          rw [← Finset.mul_sum]
      _ = lam * w i - w i₀ / v i₀ * (lam * v i) := by rw [hwE i, hvE i]
      _ = lam * (w i - w i₀ / v i₀ * v i) := by ring
  have hi₀ : w i₀ - w i₀ / v i₀ * v i₀ = 0 := by
    have hne : v i₀ ≠ 0 := ne_of_gt (hv i₀)
    field_simp
    ring
  have hall := eq_zero_of_nonneg_of_eigen_of_zero hA hz hzE hi₀
  intro i
  linarith [hall i]

/-- **Uniqueness up to scale.** -/
theorem pos_eigenvector_unique {A : ι → ι → ℝ} (hA : ∀ i j, 0 < A i j)
    {v w : ι → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    {lam mu : ℝ}
    (hvE : ∀ i, ∑ j, A i j * v j = lam * v i)
    (hwE : ∀ i, ∑ j, A i j * w j = mu * w i) :
    lam = mu ∧ ∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * v i := by
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hlam : 0 < lam := eigenvalue_pos hA hv hvE
  have hmu : 0 < mu := eigenvalue_pos hA hw hwE
  have hA' : ∀ i j, 0 ≤ A i j := fun i j => le_of_lt (hA i j)
  have h1 : |mu| ≤ lam :=
    abs_eigenvalue_le_of_pos_eigenvector A hA' v hv lam hvE w i₁ (ne_of_gt (hw i₁)) mu hwE
  have h2 : |lam| ≤ mu :=
    abs_eigenvalue_le_of_pos_eigenvector A hA' w hw mu hwE v i₁ (ne_of_gt (hv i₁)) lam hvE
  rw [abs_of_pos hmu] at h1
  rw [abs_of_pos hlam] at h2
  have heq : lam = mu := le_antisymm h2 h1
  refine ⟨heq, ?_⟩
  subst heq
  obtain ⟨c, hcw⟩ := eigenvector_eq_smul_of_pos hA hv hvE hwE
  refine ⟨c, ?_, hcw⟩
  have hwi := hw i₁
  rw [hcw i₁] at hwi
  nlinarith [hwi, hv i₁]

/-! ### §3  Existence, by compactness -/

/-- The simplex, spelled out so that no library convention is assumed. -/
def simplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem simplexSet_le_one {x : ι → ℝ} (hx : x ∈ simplexSet ι) (i : ι) : x i ≤ 1 := by
  obtain ⟨hnn, hsum⟩ := hx
  calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    _ = 1 := hsum

theorem isCompact_simplexSet : IsCompact (simplexSet ι) := by
  have hsub : simplexSet ι ⊆ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1) := by
    intro x hx
    rw [Set.mem_univ_pi]
    exact fun i => ⟨hx.1 i, simplexSet_le_one hx i⟩
  have hclosed : IsClosed (simplexSet ι) := by
    have h1 : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
      have : {x : ι → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x : ι → ℝ | 0 ≤ x i} := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {x : ι → ℝ | ∑ i, x i = 1} :=
      isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc) hclosed hsub

/-- **A strictly positive eigenvector exists.** -/
theorem exists_pos_eigenvector (A : ι → ι → ℝ) (hA : ∀ i j, 0 < A i j) :
    ∃ (v : ι → ℝ) (lam : ℝ), (∀ i, 0 < v i) ∧ (∑ i, v i = 1) ∧ 0 < lam ∧
      ∀ i, ∑ j, A i j * v j = lam * v i := by
  classical
  obtain ⟨pmax, -, hmaxp⟩ :=
    Finset.exists_max_image Finset.univ (fun p : ι × ι => A p.1 p.2)
      ⟨Classical.arbitrary (ι × ι), Finset.mem_univ _⟩
  set be : ℝ := A pmax.1 pmax.2 with hbe
  have hbe_pos : 0 < be := hA _ _
  have hhigh : ∀ i j, A i j ≤ be := fun i j => hmaxp (i, j) (Finset.mem_univ _)
  set R : ℝ := ∑ _j : ι, be with hR
  have hRnn : (0:ℝ) ≤ R := Finset.sum_nonneg fun _ _ => le_of_lt hbe_pos
  -- summing the constraint bounds `r`
  have hbound : ∀ (r : ℝ) (x : ι → ℝ), x ∈ simplexSet ι →
      (∀ i, r * x i ≤ ∑ j, A i j * x j) → r ≤ R := by
    intro r x hx hcon
    have hlhs : ∑ i, r * x i = r := by
      rw [← Finset.mul_sum, hx.2, mul_one]
    have hrhs : ∑ i, (∑ j, A i j * x j) ≤ R := by
      refine Finset.sum_le_sum fun i _ => ?_
      calc ∑ j, A i j * x j ≤ ∑ j, be * x j :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hhigh i j) (hx.1 j)
        _ = be := by rw [← Finset.mul_sum, hx.2, mul_one]
    have hmid : ∑ i, r * x i ≤ ∑ i, (∑ j, A i j * x j) :=
      Finset.sum_le_sum fun i _ => hcon i
    rw [hlhs] at hmid
    exact le_trans hmid hrhs
  set K : Set (ℝ × (ι → ℝ)) :=
    {p | p.1 ∈ Set.Icc (0:ℝ) R ∧ p.2 ∈ simplexSet ι ∧
      ∀ i, p.1 * p.2 i ≤ ∑ j, A i j * p.2 j} with hK
  -- a point of the simplex
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set e0 : ι → ℝ := fun i => if i = i₀ then 1 else 0 with he0
  have he0mem : e0 ∈ simplexSet ι := by
    constructor
    · intro i; rw [he0]; dsimp only; split <;> norm_num
    · rw [he0]; simp
  have hKne : K.Nonempty := by
    refine ⟨(0, e0), ⟨le_refl 0, hRnn⟩, he0mem, ?_⟩
    intro i
    rw [zero_mul]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (le_of_lt (hA i j)) (he0mem.1 j)
  have hclosed : IsClosed {p : ℝ × (ι → ℝ) | ∀ i, p.1 * p.2 i ≤ ∑ j, A i j * p.2 j} := by
    have hrw : {p : ℝ × (ι → ℝ) | ∀ i, p.1 * p.2 i ≤ ∑ j, A i j * p.2 j}
        = ⋂ i, {p : ℝ × (ι → ℝ) | p.1 * p.2 i ≤ ∑ j, A i j * p.2 j} := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrw]
    refine isClosed_iInter fun i => isClosed_le ?_ ?_
    · exact continuous_fst.mul ((continuous_apply i).comp continuous_snd)
    · exact continuous_finset_sum _ fun j _ =>
        continuous_const.mul ((continuous_apply j).comp continuous_snd)
  have hKeq : K = (Set.Icc (0:ℝ) R ×ˢ simplexSet ι) ∩
      {p : ℝ × (ι → ℝ) | ∀ i, p.1 * p.2 i ≤ ∑ j, A i j * p.2 j} := by
    ext p
    simp only [hK, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
    tauto
  have hKc : IsCompact K := by
    rw [hKeq]
    exact (isCompact_Icc.prod isCompact_simplexSet).inter_right hclosed
  obtain ⟨p₀, hp₀K, hp₀max⟩ := hKc.exists_isMaxOn hKne continuous_fst.continuousOn
  obtain ⟨hlamIcc, hvS, hineq⟩ := hp₀K
  have hvnn : ∀ i, 0 ≤ p₀.2 i := hvS.1
  have hvsum : ∑ i, p₀.2 i = 1 := hvS.2
  obtain ⟨j₁, hj₁⟩ : ∃ j, 0 < p₀.2 j := by
    by_contra hcon
    push_neg at hcon
    have : ∑ i, p₀.2 i = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (hcon i) (hvnn i)
    rw [hvsum] at this
    exact one_ne_zero this
  -- the image is strictly positive
  have hApos : ∀ i, 0 < ∑ j, A i j * p₀.2 j := fun i =>
    apply_pos_of_nonneg hA hvnn hj₁ i
  -- maximality forces equality
  have hEq : ∀ i, ∑ j, A i j * p₀.2 j = p₀.1 * p₀.2 i := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i₁, hi₁⟩ := hcon
    have hznn : ∀ i, 0 ≤ (∑ j, A i j * p₀.2 j) - p₀.1 * p₀.2 i := fun i =>
      sub_nonneg.mpr (hineq i)
    have hzpos : 0 < (∑ j, A i₁ j * p₀.2 j) - p₀.1 * p₀.2 i₁ :=
      lt_of_le_of_ne (hznn i₁) (Ne.symm (sub_ne_zero.mpr hi₁))
    set T : ℝ := ∑ i, (∑ j, A i j * p₀.2 j) with hT
    have hTpos : 0 < T := Finset.sum_pos (fun i _ => hApos i) ⟨i₀, Finset.mem_univ _⟩
    set y : ι → ℝ := fun i => (∑ j, A i j * p₀.2 j) / T with hy
    have hypos : ∀ i, 0 < y i := fun i => div_pos (hApos i) hTpos
    have hymem : y ∈ simplexSet ι := by
      refine ⟨fun i => le_of_lt (hypos i), ?_⟩
      rw [hy, ← Finset.sum_div, ← hT, div_self (ne_of_gt hTpos)]
    -- one more application of A improves strictly
    have hstrict : ∀ i, p₀.1 * y i < ∑ j, A i j * y j := by
      intro i
      have hsplit : ∑ j, A i j * (∑ k, A j k * p₀.2 k)
          = p₀.1 * (∑ j, A i j * p₀.2 j)
            + ∑ j, A i j * ((∑ k, A j k * p₀.2 k) - p₀.1 * p₀.2 j) := by
        calc ∑ j, A i j * (∑ k, A j k * p₀.2 k)
            = ∑ j, (A i j * (p₀.1 * p₀.2 j)
                + A i j * ((∑ k, A j k * p₀.2 k) - p₀.1 * p₀.2 j)) :=
              Finset.sum_congr rfl fun j _ => by ring
          _ = (∑ j, A i j * (p₀.1 * p₀.2 j))
                + ∑ j, A i j * ((∑ k, A j k * p₀.2 k) - p₀.1 * p₀.2 j) :=
              Finset.sum_add_distrib
          _ = p₀.1 * (∑ j, A i j * p₀.2 j)
                + ∑ j, A i j * ((∑ k, A j k * p₀.2 k) - p₀.1 * p₀.2 j) := by
              congr 1
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
      have hzp : 0 < ∑ j, A i j * ((∑ k, A j k * p₀.2 k) - p₀.1 * p₀.2 j) :=
        apply_pos_of_nonneg hA hznn hzpos i
      have hkey : p₀.1 * (∑ j, A i j * p₀.2 j)
          < ∑ j, A i j * (∑ k, A j k * p₀.2 k) := by linarith [hsplit, hzp]
      have hsum : ∑ j, A i j * y j = (∑ j, A i j * (∑ k, A j k * p₀.2 k)) / T := by
        rw [hy, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hy, hsum, show p₀.1 * ((∑ j, A i j * p₀.2 j) / T)
            = (p₀.1 * ∑ j, A i j * p₀.2 j) / T from by ring,
        div_lt_div_iff₀ hTpos hTpos]
      nlinarith [hkey, hTpos]
    obtain ⟨i₂, -, hi₂⟩ :=
      Finset.exists_min_image Finset.univ
        (fun i => ((∑ j, A i j * y j) - p₀.1 * y i) / y i)
        ⟨i₀, Finset.mem_univ _⟩
    set eps : ℝ := ((∑ j, A i₂ j * y j) - p₀.1 * y i₂) / y i₂ with heps
    have hepspos : 0 < eps := by
      rw [heps]
      exact div_pos (by linarith [hstrict i₂]) (hypos i₂)
    have hnew : ∀ i, (p₀.1 + eps) * y i ≤ ∑ j, A i j * y j := by
      intro i
      have hle' := hi₂ i (Finset.mem_univ _)
      have hmul : eps * y i ≤ (∑ j, A i j * y j) - p₀.1 * y i :=
        (le_div_iff₀ (hypos i)).mp hle'
      have hexp : (p₀.1 + eps) * y i = p₀.1 * y i + eps * y i := by ring
      linarith [hmul, hexp]
    have hRb : p₀.1 + eps ≤ R := hbound _ y hymem hnew
    have hmem : ((p₀.1 + eps), y) ∈ K :=
      ⟨⟨by linarith [hepspos, hlamIcc.1], hRb⟩, hymem, hnew⟩
    have hcontra : p₀.1 + eps ≤ p₀.1 := hp₀max hmem
    linarith [hepspos, hcontra]
  -- the maximiser is strictly positive
  have hlampos : 0 < p₀.1 := by
    have h1 := hApos i₀
    rw [hEq i₀] at h1
    nlinarith [h1, hvnn i₀, hApos i₀]
  have hvpos : ∀ i, 0 < p₀.2 i := by
    intro i
    have h1 := hApos i
    rw [hEq i] at h1
    nlinarith [h1, hlampos, hvnn i]
  exact ⟨p₀.2, p₀.1, hvpos, hvsum, hlampos, hEq⟩

/-! ### §3b  The normalised transfer operator fixes the vacuum -/

/-- The kernel divided by its own eigenvalue: the transfer operator for which
the Perron vector is a genuine fixed point. -/
noncomputable def normalizedKernel (A : ι → ι → ℝ) (lam : ℝ) (i j : ι) : ℝ :=
  A i j / lam

/-- **`T Ω = Ω`.**  Companion papers obtained the vacuum from the property that
the *uniform* vector is fixed by the normalised kernel, and O-3f proved that
property FAILS once a spatial coupling is present.  Here the same equation holds
again --- for the Perron vector rather than the uniform one. -/
theorem normalizedKernel_fixes_eigenvector {A : ι → ι → ℝ} {v : ι → ℝ} {lam : ℝ}
    (hlam : lam ≠ 0) (hvE : ∀ i, ∑ j, A i j * v j = lam * v i) :
    ∀ i, ∑ j, normalizedKernel A lam i j * v j = v i := by
  intro i
  unfold normalizedKernel
  have hsplit : ∑ j, A i j / lam * v j = (∑ j, A i j * v j) / lam := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hvE i]
  field_simp

/-- **The normalised vacuum, packaged.**  A strictly positive `Ω` with
`∑ Ω = 1` fixed by the normalised transfer operator. -/
theorem exists_normalized_vacuum (A : ι → ι → ℝ) (hA : ∀ i j, 0 < A i j) :
    ∃ (Om : ι → ℝ) (lam : ℝ), (∀ i, 0 < Om i) ∧ (∑ i, Om i = 1) ∧ 0 < lam ∧
      ∀ i, ∑ j, normalizedKernel A lam i j * Om j = Om i := by
  obtain ⟨v, lam, hvpos, hvsum, hlampos, hvE⟩ := exists_pos_eigenvector A hA
  exact ⟨v, lam, hvpos, hvsum, hlampos,
    normalizedKernel_fixes_eigenvector (ne_of_gt hlampos) hvE⟩

end PositiveKernel

/-! ### §4  The vacuum at every spatial extent -/

/-- The decoupled kernel of O-3f times an arbitrary weight on the **source**
configuration, at arbitrary spatial extent. -/
noncomputable def sourceWeightedKernelL {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (σ τ : Fin L → Fin 2) : ℝ :=
  w σ * spatialKernel β σ τ

theorem sourceWeightedKernelL_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (σ τ : Fin L → Fin 2) :
    0 < sourceWeightedKernelL w β σ τ :=
  mul_pos (hw σ) (spatialKernel_pos β σ τ)

/-- **THE VACUUM AT EVERY SPATIAL EXTENT.**  For every `L`, every `β` and every
strictly positive source weight, the kernel has a strictly positive eigenvector
with a strictly positive eigenvalue.  This is the object O-3f showed the
elementary route stops producing: it was never absent, only unavailable to that
route. -/
theorem vacuum_exists_of_sourceWeight {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) :
    ∃ (v : (Fin L → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < v σ) ∧ (∑ σ, v σ = 1) ∧
      0 < lam ∧
      ∀ σ, ∑ τ : Fin L → Fin 2, sourceWeightedKernelL w β σ τ * v τ = lam * v σ :=
  exists_pos_eigenvector _ (sourceWeightedKernelL_pos hw β)

/-- **THE NORMALISED VACUUM AT EVERY SPATIAL EXTENT.**  `T Ω = Ω` with `Ω > 0`
and `∑ Ω = 1`, for every `L` and every strictly positive source weight.  O-3f
proved this equation false for the *uniform* `Ω` as soon as a coupling is
present; it is true again for the Perron `Ω`, at every extent. -/
theorem normalized_vacuum_of_sourceWeight {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) :
    ∃ (Om : (Fin L → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < Om σ) ∧ (∑ σ, Om σ = 1) ∧
      0 < lam ∧
      ∀ σ, ∑ τ : Fin L → Fin 2,
        normalizedKernel (sourceWeightedKernelL w β) lam σ τ * Om τ = Om σ :=
  exists_normalized_vacuum _ (sourceWeightedKernelL_pos hw β)

/-- **Unique up to scale, with a common eigenvalue.** -/
theorem vacuum_unique_of_sourceWeight {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v u : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) (hu : ∀ σ, 0 < u σ)
    {lam mu : ℝ}
    (hvE : ∀ σ, ∑ τ : Fin L → Fin 2, sourceWeightedKernelL w β σ τ * v τ = lam * v σ)
    (huE : ∀ σ, ∑ τ : Fin L → Fin 2, sourceWeightedKernelL w β σ τ * u τ = mu * u σ) :
    lam = mu ∧ ∃ c : ℝ, 0 < c ∧ ∀ σ, u σ = c * v σ :=
  pos_eigenvector_unique (sourceWeightedKernelL_pos hw β) hv hu hvE huE

/-- **And its eigenvalue is the spectral radius**, by the complex
domination result of O-3h. -/
theorem vacuum_spectral_radius_of_sourceWeight {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) {lam : ℝ}
    (hvE : ∀ σ, ∑ τ : Fin L → Fin 2, sourceWeightedKernelL w β σ τ * v τ = lam * v σ)
    (u : (Fin L → Fin 2) → ℂ) (σ₁ : Fin L → Fin 2) (hu : u σ₁ ≠ 0) (mu : ℂ)
    (hmu : ∀ σ : Fin L → Fin 2,
      ∑ τ : Fin L → Fin 2, ((sourceWeightedKernelL w β σ τ : ℝ) : ℂ) * u τ = mu * u σ) :
    ‖mu‖ ≤ lam :=
  norm_eigenvalue_le_of_pos_eigenvector _
    (fun σ τ => le_of_lt (sourceWeightedKernelL_pos hw β σ τ)) v hv lam hvE u σ₁ hu mu hmu

/-- The spatial weight with one bond around a slice of extent `L + 1`. -/
noncomputable def spatialWeightRing (γ : ℝ) {L : ℕ} (σ : Fin (L + 1) → Fin 2) : ℝ :=
  ∏ j : Fin (L + 1), z2Bond γ (σ j) (σ (j + 1))

theorem spatialWeightRing_pos (γ : ℝ) {L : ℕ} (σ : Fin (L + 1) → Fin 2) :
    0 < spatialWeightRing γ σ := by
  unfold spatialWeightRing
  exact Finset.prod_pos fun j _ => z2Bond_pos γ _ _

/-- **The concrete coupled slice, at every extent, has its vacuum.** -/
theorem coupled_ring_vacuum_exists (β γ : ℝ) (L : ℕ) :
    ∃ (v : (Fin (L + 1) → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < v σ) ∧
      (∑ σ, v σ = 1) ∧ 0 < lam ∧
      ∀ σ, ∑ τ : Fin (L + 1) → Fin 2,
        sourceWeightedKernelL (spatialWeightRing γ) β σ τ * v τ = lam * v σ :=
  vacuum_exists_of_sourceWeight (spatialWeightRing_pos γ) β

/-- **And the ring slice has its normalised vacuum, at every extent.** -/
theorem coupled_ring_normalized_vacuum (β γ : ℝ) (L : ℕ) :
    ∃ (Om : (Fin (L + 1) → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < Om σ) ∧
      (∑ σ, Om σ = 1) ∧ 0 < lam ∧
      ∀ σ, ∑ τ : Fin (L + 1) → Fin 2,
        normalizedKernel (sourceWeightedKernelL (spatialWeightRing γ) β) lam σ τ
          * Om τ = Om σ :=
  normalized_vacuum_of_sourceWeight (spatialWeightRing_pos γ) β

end YangMills.OS
