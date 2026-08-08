/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116FiniteMultiaffineInterpolation
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Coordinate jets of finite multiaffine interpolants

This file isolates the algebraic differential mechanism used by the physical
Faà di Bruno expansion.  For a globally smooth separately affine function,
the Fréchet derivative in a canonical coordinate direction is its literal
unit finite difference.  Taking a finite difference preserves separate
affinity and differentiability, so the statement can be iterated without
reintroducing any physical analytic hypothesis.
-/

namespace YangMills.RG

noncomputable section

/-- A function on a finite real coordinate space is affine in each
coordinate separately. -/
def CMP116CoordinateAffine
    {D E : Type*} [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]
    (f : (D → ℝ) → E) : Prop :=
  ∀ (s : D → ℝ) (d : D) (t : ℝ),
    f (Function.update s d t) =
      (1 - t) • f (Function.update s d 0) +
        t • f (Function.update s d 1)

/-- Literal unit finite difference in one coordinate. -/
def cmp116CoordinateFiniteDifference
    {D E : Type*} [DecidableEq D]
    [AddCommGroup E]
    (f : (D → ℝ) → E) (d : D) (s : D → ℝ) : E :=
  f (Function.update s d 1) - f (Function.update s d 0)

/-- Replacing one coordinate by a constant is smooth. -/
theorem contDiff_cmp116UpdateConstMap
    {D : Type*} [Fintype D] [DecidableEq D]
    (n : WithTop ℕ∞) (d : D) (t : ℝ) :
    ContDiff ℝ n (fun s : D → ℝ => Function.update s d t) := by
  apply contDiff_pi'
  intro i
  by_cases hid : i = d
  · subst i
    simpa using (contDiff_const : ContDiff ℝ n (fun _ : D → ℝ => t))
  · simpa [Function.update_of_ne hid] using
      (contDiff_apply (n := n) ℝ ℝ i :
        ContDiff ℝ n (fun s : D → ℝ => s i))

/-- Unit finite difference preserves all available differentiability. -/
theorem ContDiff.cmp116CoordinateFiniteDifference
    {D E : Type*} [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : (D → ℝ) → E}
    (hf : ContDiff ℝ n f) (d : D) :
    ContDiff ℝ n (cmp116CoordinateFiniteDifference f d) := by
  unfold YangMills.RG.cmp116CoordinateFiniteDifference
  exact
    (hf.comp (contDiff_cmp116UpdateConstMap n d 1)).sub
      (hf.comp (contDiff_cmp116UpdateConstMap n d 0))

/-- Unit finite difference in one coordinate preserves separate affinity in
every coordinate. -/
theorem CMP116CoordinateAffine.coordinateFiniteDifference
    {D E : Type*} [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]
    {f : (D → ℝ) → E}
    (hf : CMP116CoordinateAffine f) (d : D) :
    CMP116CoordinateAffine (cmp116CoordinateFiniteDifference f d) := by
  intro s e t
  by_cases hed : e = d
  · subst e
    simp [cmp116CoordinateFiniteDifference]
    module
  · have hcomm (z w : ℝ) :
        Function.update (Function.update s e z) d w =
          Function.update (Function.update s d w) e z := by
      have hde : d ≠ e := Ne.symm hed
      funext x
      by_cases hxd : x = d
      · subst x
        simp [Function.update, hde]
      · by_cases hxe : x = e
        · subst x
          simp [Function.update, hed]
        · simp [Function.update, hxd, hxe]
    unfold cmp116CoordinateFiniteDifference
    rw [hcomm t 1, hcomm t 0, hf (Function.update s d 1) e t,
      hf (Function.update s d 0) e t]
    rw [hcomm 0 1, hcomm 1 1, hcomm 0 0, hcomm 1 0]
    module

/-- The derivative in a canonical coordinate direction of a smooth,
separately affine function is its literal unit finite difference. -/
theorem fderiv_apply_single_eq_cmp116CoordinateFiniteDifference
    {D E : Type*} [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (D → ℝ) → E)
    (hf : CMP116CoordinateAffine f)
    (hfdiff : Differentiable ℝ f)
    (s : D → ℝ) (d : D) :
    fderiv ℝ f s (Pi.single d 1) =
      cmp116CoordinateFiniteDifference f d s := by
  have hchain :
      HasDerivAt
        (fun t => f (Function.update s d t))
        (fderiv ℝ f s (Pi.single d 1)) (s d) := by
    have hupdate :
        HasDerivAt (Function.update s d) (Pi.single d 1) (s d) := by
      convert (hasFDerivAt_update s (s d)).hasDerivAt using 1
      ext i
      by_cases hi : i = d
      · subst i
        simp
      · simp [hi]
    have h :=
      (hfdiff (Function.update s d (s d))).hasFDerivAt.comp_hasDerivAt (s d)
        hupdate
    simpa [Function.comp_def] using h
  have haffine :
      (fun t => f (Function.update s d t)) =
        fun t =>
          f (Function.update s d 0) +
            t • cmp116CoordinateFiniteDifference f d s := by
    funext t
    rw [hf s d t]
    unfold cmp116CoordinateFiniteDifference
    module
  have hrhs :
      HasDerivAt
        (fun t =>
          f (Function.update s d 0) +
            t • cmp116CoordinateFiniteDifference f d s)
        (cmp116CoordinateFiniteDifference f d s) (s d) := by
    have hraw :=
      ((hasDerivAt_id (𝕜 := ℝ) (s d)).smul_const
        (cmp116CoordinateFiniteDifference f d s)).const_add
          (f (Function.update s d 0))
    simpa only [id_eq, one_smul] using hraw
  rw [haffine] at hchain
  exact hchain.unique hrhs

/-- A noduplicated finite vertex interpolant is separately affine in every
ambient coordinate: listed coordinates use its defining affine identity,
while absent coordinates are constant. -/
theorem cmp116CoordinateAffine_finiteMultiaffineInterpolation
    {D E : Type*} [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]
    (f : (D → ℝ) → E) (base : D → ℝ)
    (L : List D) (hL : L.Nodup) :
    CMP116CoordinateAffine
      (cmp116FiniteMultiaffineInterpolation f base L) := by
  intro s d t
  by_cases hdL : d ∈ L
  · exact
      cmp116FiniteMultiaffineInterpolation_update_eq_affine
        f base L hL s d hdL t
  · rw [
      cmp116FiniteMultiaffineInterpolation_update_of_not_mem
        f base L s d t hdL,
      cmp116FiniteMultiaffineInterpolation_update_of_not_mem
        f base L s d 0 hdL,
      cmp116FiniteMultiaffineInterpolation_update_of_not_mem
        f base L s d 1 hdL]
    module

/-- Generic first-jet formula for the finite multiaffine interpolant. -/
theorem
    fderiv_cmp116FiniteMultiaffineInterpolation_apply_single_eq_finiteDifference
    {D E : Type*} [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (D → ℝ) → E) (base : D → ℝ)
    (L : List D) (hL : L.Nodup)
    (s : D → ℝ) (d : D) :
    fderiv ℝ
        (cmp116FiniteMultiaffineInterpolation f base L)
        s (Pi.single d 1) =
      cmp116CoordinateFiniteDifference
        (cmp116FiniteMultiaffineInterpolation f base L) d s := by
  apply fderiv_apply_single_eq_cmp116CoordinateFiniteDifference
  · exact cmp116CoordinateAffine_finiteMultiaffineInterpolation
      f base L hL
  · exact
      (contDiff_cmp116FiniteMultiaffineInterpolation
        1 f base L).differentiable one_ne_zero

/-- Iterated unit finite difference, recursively removing the last indexed
coordinate.  This ordering matches `iteratedFDeriv_succ_apply_right`. -/
noncomputable def cmp116IteratedCoordinateFiniteDifference
    {D E : Type*} [DecidableEq D]
    [AddCommGroup E]
    (n : ℕ) (f : (D → ℝ) → E) (coordinates : Fin n → D) :
    (D → ℝ) → E :=
  match n with
  | 0 => f
  | n + 1 =>
      cmp116IteratedCoordinateFiniteDifference n
        (cmp116CoordinateFiniteDifference f (coordinates (Fin.last n)))
        (fun i => coordinates i.castSucc)

/-- Vertex of the finite coordinate cube, using the same last-coordinate
recursion as the iterated finite difference. -/
def cmp116CoordinateCubePoint
    {D : Type*} [DecidableEq D]
    (n : ℕ) (coordinates : Fin n → D)
    (s : D → ℝ) (bits : Fin n → Bool) : D → ℝ :=
  match n with
  | 0 => s
  | n + 1 =>
      Function.update
        (cmp116CoordinateCubePoint n
          (fun i => coordinates i.castSucc) s
          (fun i => bits i.castSucc))
        (coordinates (Fin.last n))
        (if bits (Fin.last n) then 1 else 0)

/-- Two functions agree on every vertex of one finite coordinate cube. -/
def CMP116AgreeOnCoordinateCube
    {D E : Type*} [DecidableEq D]
    (n : ℕ) (coordinates : Fin n → D) (s : D → ℝ)
    (f g : (D → ℝ) → E) : Prop :=
  ∀ bits : Fin n → Bool,
    f (cmp116CoordinateCubePoint n coordinates s bits) =
      g (cmp116CoordinateCubePoint n coordinates s bits)

/-- Pointwise equality on the finite coordinate cube is exactly the amount
of equality needed by the iterated finite-difference functional. -/
theorem cmp116IteratedCoordinateFiniteDifference_congr_on_cube
    {D E : Type*} [DecidableEq D]
    [AddCommGroup E]
    (n : ℕ) (coordinates : Fin n → D) (s : D → ℝ)
    (f g : (D → ℝ) → E)
    (hfg : CMP116AgreeOnCoordinateCube n coordinates s f g) :
    cmp116IteratedCoordinateFiniteDifference n f coordinates s =
      cmp116IteratedCoordinateFiniteDifference n g coordinates s := by
  induction n generalizing f g with
  | zero =>
      simpa [cmp116IteratedCoordinateFiniteDifference,
        CMP116AgreeOnCoordinateCube, cmp116CoordinateCubePoint] using
        hfg (fun i => Fin.elim0 i)
  | succ n ih =>
      let dlast := coordinates (Fin.last n)
      let initCoordinates : Fin n → D :=
        fun i => coordinates i.castSucc
      have hdiff :
          CMP116AgreeOnCoordinateCube n initCoordinates s
            (cmp116CoordinateFiniteDifference f dlast)
            (cmp116CoordinateFiniteDifference g dlast) := by
        intro bits
        have hzero := hfg (Fin.lastCases false bits)
        have hone := hfg (Fin.lastCases true bits)
        unfold CMP116AgreeOnCoordinateCube at hfg
        unfold cmp116CoordinateFiniteDifference
        change
          f (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 1) -
              f (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 0) =
            g (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 1) -
              g (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 0)
        have hzero' :
            f (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 0) =
              g (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 0) := by
          simpa [cmp116CoordinateCubePoint, initCoordinates, dlast] using
            hzero
        have hone' :
            f (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 1) =
              g (Function.update
                (cmp116CoordinateCubePoint n initCoordinates s bits)
                dlast 1) := by
          simpa [cmp116CoordinateCubePoint, initCoordinates, dlast] using
            hone
        rw [hzero', hone']
      simpa [cmp116IteratedCoordinateFiniteDifference,
        initCoordinates, dlast] using
        ih initCoordinates
          (cmp116CoordinateFiniteDifference f dlast)
          (cmp116CoordinateFiniteDifference g dlast)
          hdiff

/-- A predicate stable under setting any coordinate to either cube endpoint
holds at every vertex of the finite coordinate cube. -/
theorem cmp116CoordinateCubePoint_property
    {D : Type*} [DecidableEq D]
    (P : (D → ℝ) → Prop)
    (hstable : ∀ (u : D → ℝ) (d : D), P u →
      P (Function.update u d 0) ∧ P (Function.update u d 1))
    (n : ℕ) (coordinates : Fin n → D)
    (s : D → ℝ) (hs : P s) :
    ∀ bits : Fin n → Bool,
      P (cmp116CoordinateCubePoint n coordinates s bits) := by
  induction n with
  | zero =>
      intro bits
      simpa [cmp116CoordinateCubePoint] using hs
  | succ n ih =>
      intro bits
      let initCoordinates : Fin n → D :=
        fun i => coordinates i.castSucc
      let initBits : Fin n → Bool :=
        fun i => bits i.castSucc
      have hinit :
          P (cmp116CoordinateCubePoint n initCoordinates s initBits) :=
        ih initCoordinates initBits
      by_cases hbit : bits (Fin.last n) = true
      · simpa [cmp116CoordinateCubePoint, initCoordinates, initBits,
          hbit] using
          (hstable
            (cmp116CoordinateCubePoint n initCoordinates s initBits)
            (coordinates (Fin.last n)) hinit).2
      · have hfalse : bits (Fin.last n) = false := Bool.eq_false_iff.mpr hbit
        simpa [cmp116CoordinateCubePoint, initCoordinates, initBits,
          hfalse] using
          (hstable
            (cmp116CoordinateCubePoint n initCoordinates s initBits)
            (coordinates (Fin.last n)) hinit).1

/-- Carrier obtained by inserting the indexed coordinates in the same order
as the iterated finite-difference recursion. -/
def cmp116IteratedCoordinateCarrier
    {D : Type*} [DecidableEq D]
    (n : ℕ) (coordinates : Fin n → D) (S : Finset D) : Finset D :=
  match n with
  | 0 => S
  | n + 1 =>
      cmp116IteratedCoordinateCarrier n
        (fun i => coordinates i.castSucc)
        (insert (coordinates (Fin.last n)) S)

/-- Source-facing freshness condition matching the recursive carrier:
every newly inserted coordinate is fresh at its insertion step. -/
def CMP116IteratedCoordinatesFresh
    {D : Type*} [DecidableEq D]
    (n : ℕ) (coordinates : Fin n → D) (S : Finset D) : Prop :=
  match n with
  | 0 => True
  | n + 1 =>
      coordinates (Fin.last n) ∉ S ∧
        CMP116IteratedCoordinatesFresh n
          (fun i => coordinates i.castSucc)
          (insert (coordinates (Fin.last n)) S)

/-- Injective coordinates initially disjoint from the carrier satisfy the
recursive source-facing freshness condition. -/
theorem cmp116IteratedCoordinatesFresh_of_injective_not_mem
    {D : Type*} [DecidableEq D]
    (n : ℕ) (coordinates : Fin n → D) (S : Finset D)
    (hinjective : Function.Injective coordinates)
    (hnotmem : ∀ i, coordinates i ∉ S) :
    CMP116IteratedCoordinatesFresh n coordinates S := by
  induction n generalizing S with
  | zero =>
      simp [CMP116IteratedCoordinatesFresh]
  | succ n ih =>
      let dlast := coordinates (Fin.last n)
      let initCoordinates : Fin n → D :=
        fun i => coordinates i.castSucc
      have hlast : dlast ∉ S := hnotmem (Fin.last n)
      have hinitInjective : Function.Injective initCoordinates := by
        intro i j hij
        exact Fin.castSucc_injective n
          (hinjective hij)
      have hinitNotMem :
          ∀ i, initCoordinates i ∉ insert dlast S := by
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with heq | hiS
        · have hindex :
              (i.castSucc : Fin (n + 1)) = Fin.last n :=
            hinjective heq
          exact Fin.castSucc_ne_last i hindex
        · exact hnotmem i.castSucc hiS
      exact ⟨hlast,
        ih initCoordinates (insert dlast S)
          hinitInjective hinitNotMem⟩

/-- Iterated coordinate finite differences retain separate affinity. -/
theorem CMP116CoordinateAffine.iteratedCoordinateFiniteDifference
    {D E : Type*} [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]
    {f : (D → ℝ) → E}
    (hf : CMP116CoordinateAffine f) :
  ∀ (n : ℕ) (coordinates : Fin n → D),
      CMP116CoordinateAffine
        (cmp116IteratedCoordinateFiniteDifference n f coordinates) := by
  intro n
  induction n generalizing f with
  | zero =>
      intro coordinates
      simpa [cmp116IteratedCoordinateFiniteDifference] using hf
  | succ n ih =>
      intro coordinates
      simp only [cmp116IteratedCoordinateFiniteDifference]
      exact ih
        (hf.coordinateFiniteDifference (coordinates (Fin.last n)))
        (fun i => coordinates i.castSucc)

/-- Iterated coordinate finite differences retain the differentiability
order of the original function. -/
theorem ContDiff.iteratedCoordinateFiniteDifference
    {D E : Type*} [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : WithTop ℕ∞} {f : (D → ℝ) → E}
    (hf : ContDiff ℝ N f) :
  ∀ (n : ℕ) (coordinates : Fin n → D),
      ContDiff ℝ N
        (cmp116IteratedCoordinateFiniteDifference n f coordinates) := by
  intro n
  induction n generalizing f with
  | zero =>
      intro coordinates
      simpa [cmp116IteratedCoordinateFiniteDifference] using hf
  | succ n ih =>
      intro coordinates
      simp only [cmp116IteratedCoordinateFiniteDifference]
      exact ih
        (ContDiff.cmp116CoordinateFiniteDifference hf
          (coordinates (Fin.last n)))
        (fun i => coordinates i.castSucc)

set_option maxHeartbeats 2000000 in
/-- Arbitrary coordinate jet of a smooth separately affine function equals
its iterated literal unit finite difference.  Repeated coordinates are
allowed; separate affinity then makes the corresponding higher difference
zero automatically. -/
theorem iteratedFDeriv_apply_single_eq_iteratedCoordinateFiniteDifference
    {D E : Type*} [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : (D → ℝ) → E)
    (coordinates : Fin n → D)
    (hf : CMP116CoordinateAffine f)
    (hfdiff : ContDiff ℝ n f)
    (s : D → ℝ) :
    iteratedFDeriv ℝ n f s
        (fun i => Pi.single (coordinates i) 1) =
      cmp116IteratedCoordinateFiniteDifference n f coordinates s := by
  induction n generalizing f with
  | zero =>
      simp [cmp116IteratedCoordinateFiniteDifference]
  | succ n ih =>
      let dlast := coordinates (Fin.last n)
      let initCoordinates : Fin n → D :=
        fun i => coordinates i.castSucc
      have hfdiffRight :
          ContDiff ℝ n (fderiv ℝ f) := by
        exact hfdiff.fderiv_right (m := (n : WithTop ℕ∞)) (by norm_num)
      rw [iteratedFDeriv_succ_apply_right]
      rw [← iteratedFDeriv_clm_apply_const_apply
        hfdiffRight (show (n : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from le_rfl)]
      have hfunction :
          (fun y => fderiv ℝ f y (Pi.single dlast 1)) =
            cmp116CoordinateFiniteDifference f dlast := by
        funext y
        exact
          fderiv_apply_single_eq_cmp116CoordinateFiniteDifference
            f hf (hfdiff.differentiable (by norm_num)) y dlast
      rw [hfunction]
      have hnextAffine :
          CMP116CoordinateAffine
            (cmp116CoordinateFiniteDifference f dlast) :=
        hf.coordinateFiniteDifference dlast
      have hnextDiff :
          ContDiff ℝ n
            (cmp116CoordinateFiniteDifference f dlast) :=
        (ContDiff.cmp116CoordinateFiniteDifference hfdiff dlast).of_le
          (by norm_num)
      change
        iteratedFDeriv ℝ n
            (cmp116CoordinateFiniteDifference f dlast) s
            (fun i => Pi.single (initCoordinates i) 1) =
          cmp116IteratedCoordinateFiniteDifference n
            (cmp116CoordinateFiniteDifference f dlast)
            initCoordinates s
      exact ih
        (cmp116CoordinateFiniteDifference f dlast)
        initCoordinates hnextAffine hnextDiff

/-- Arbitrary coordinate jet of the finite vertex interpolant. -/
theorem
    iteratedFDeriv_cmp116FiniteMultiaffineInterpolation_apply_single_eq_iteratedFiniteDifference
    {D E : Type*} [Fintype D] [DecidableEq D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : (D → ℝ) → E) (base : D → ℝ)
    (L : List D) (hL : L.Nodup)
    (coordinates : Fin n → D) (s : D → ℝ) :
    iteratedFDeriv ℝ n
        (cmp116FiniteMultiaffineInterpolation f base L) s
        (fun i => Pi.single (coordinates i) 1) =
      cmp116IteratedCoordinateFiniteDifference n
        (cmp116FiniteMultiaffineInterpolation f base L)
        coordinates s := by
  apply iteratedFDeriv_apply_single_eq_iteratedCoordinateFiniteDifference
  · exact cmp116CoordinateAffine_finiteMultiaffineInterpolation
      f base L hL
  · exact contDiff_cmp116FiniteMultiaffineInterpolation n f base L

end

end YangMills.RG
