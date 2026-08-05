/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinCovariantState

/-!
# The uniform bound of the Dobrushin cylinder state

The operations already descended to the intrinsic cylinder quotient are
bundled here as a commutative real algebra.  The realization map is an
injective algebra morphism.  We then define the actual uniform norm as the
supremum of the represented global cylinder function and prove that the D-8
state is contractive for this norm.

This is the continuity input required by a later complex C-star completion.
No completion or DLR equation is asserted in this module.
-/

namespace YangMills.OS
namespace Dobrushin

open Classical Set

namespace LocalCylinderAlgebra

/-! ## Bundled commutative real algebra -/

@[simp] theorem realizeGlobal_const (c : ℝ) :
    realizeGlobal (const c) = fun _ => c := rfl

noncomputable instance : Sub LocalCylinderAlgebra :=
  ⟨fun O P => O + -P⟩

noncomputable instance : SMul ℕ LocalCylinderAlgebra :=
  ⟨fun n O => (n : ℝ) • O⟩

noncomputable instance : SMul ℤ LocalCylinderAlgebra :=
  ⟨fun n O => (n : ℝ) • O⟩

noncomputable instance : Pow LocalCylinderAlgebra ℕ :=
  ⟨fun O n => Nat.rec 1 (fun _ P => P * O) n⟩

noncomputable instance : NatCast LocalCylinderAlgebra :=
  ⟨fun n => const n⟩

noncomputable instance : IntCast LocalCylinderAlgebra :=
  ⟨fun n => const n⟩

@[simp] theorem realizeGlobal_sub (O P : LocalCylinderAlgebra) :
    realizeGlobal (O - P) = realizeGlobal O - realizeGlobal P := by
  rw [show O - P = O + -P from rfl, realizeGlobal_add, realizeGlobal_neg]
  rfl

@[simp] theorem realizeGlobal_nsmul (n : ℕ) (O : LocalCylinderAlgebra) :
    realizeGlobal (n • O) = n • realizeGlobal O := by
  change realizeGlobal ((n : ℝ) • O) = n • realizeGlobal O
  rw [realizeGlobal_smul]
  funext sigma
  simp [nsmul_eq_mul]

@[simp] theorem realizeGlobal_zsmul (n : ℤ) (O : LocalCylinderAlgebra) :
    realizeGlobal (n • O) = n • realizeGlobal O := by
  change realizeGlobal ((n : ℝ) • O) = n • realizeGlobal O
  rw [realizeGlobal_smul]
  funext sigma
  simp [zsmul_eq_mul]

@[simp] theorem realizeGlobal_pow (O : LocalCylinderAlgebra) :
    ∀ n : ℕ, realizeGlobal (O ^ n) = realizeGlobal O ^ n
  | 0 => rfl
  | n + 1 => by
      change realizeGlobal ((O ^ n) * O) = realizeGlobal O ^ (n + 1)
      rw [realizeGlobal_mul, realizeGlobal_pow]
      rfl

@[simp] theorem realizeGlobal_natCast (n : ℕ) :
    realizeGlobal (n : LocalCylinderAlgebra) = (n : InfiniteIsingConfig → ℝ) := by
  rfl

@[simp] theorem realizeGlobal_intCast (n : ℤ) :
    realizeGlobal (n : LocalCylinderAlgebra) = (n : InfiniteIsingConfig → ℝ) := by
  rfl

noncomputable instance : CommRing LocalCylinderAlgebra :=
  Function.Injective.commRing realizeGlobal realizeGlobal_injective
    realizeGlobal_zero realizeGlobal_one realizeGlobal_add realizeGlobal_mul
    realizeGlobal_neg realizeGlobal_sub realizeGlobal_nsmul realizeGlobal_zsmul
    realizeGlobal_pow realizeGlobal_natCast realizeGlobal_intCast

/-- Realization as an additive morphism. -/
noncomputable def realizeGlobalAddHom :
    LocalCylinderAlgebra →+ (InfiniteIsingConfig → ℝ) where
  toFun := realizeGlobal
  map_zero' := realizeGlobal_zero
  map_add' := realizeGlobal_add

noncomputable instance : Module ℝ LocalCylinderAlgebra :=
  Function.Injective.module ℝ realizeGlobalAddHom realizeGlobal_injective
    realizeGlobal_smul

/-- Constants as a ring morphism. -/
noncomputable def constRingHom : ℝ →+* LocalCylinderAlgebra where
  toFun := const
  map_zero' := by
    apply realizeGlobal_injective
    rfl
  map_one' := by
    apply realizeGlobal_injective
    rfl
  map_add' c d := by
    apply realizeGlobal_injective
    funext sigma
    rfl
  map_mul' c d := by
    apply realizeGlobal_injective
    funext sigma
    rfl

noncomputable instance : Algebra ℝ LocalCylinderAlgebra where
  algebraMap := constRingHom
  commutes' := fun _ O => mul_comm _ O
  smul_def' := by
    intro c O
    apply realizeGlobal_injective
    funext sigma
    rw [congrFun (realizeGlobal_smul c O) sigma,
      congrFun (realizeGlobal_mul (constRingHom c) O) sigma]
    rfl

/-- Realization is an injective real-algebra morphism. -/
noncomputable def realizeGlobalAlgHom :
    LocalCylinderAlgebra →ₐ[ℝ] (InfiniteIsingConfig → ℝ) where
  toFun := realizeGlobal
  map_one' := realizeGlobal_one
  map_mul' := realizeGlobal_mul
  map_zero' := realizeGlobal_zero
  map_add' := realizeGlobal_add
  commutes' c := by
    funext sigma
    rfl

theorem realizeGlobalAlgHom_injective :
    Function.Injective realizeGlobalAlgHom :=
  realizeGlobal_injective

/-! ## Intrinsic uniform norm -/

/-- The represented global cylinder function has bounded absolute range. -/
theorem bddAbove_abs_realizeGlobal (O : LocalCylinderAlgebra) :
    BddAbove (Set.range fun sigma => |realizeGlobal O sigma|) := by
  induction O using Quotient.inductionOn with
  | _ O =>
      let M : ℝ := Finset.univ.sup' Finset.univ_nonempty
        (fun x : O.support → Fin 2 => |O.kernel x|)
      refine ⟨M, ?_⟩
      rintro y ⟨sigma, rfl⟩
      exact Finset.le_sup'
        (fun x : O.support → Fin 2 => |O.kernel x|)
        (Finset.mem_univ (fun s => sigma s.1))

/-- Uniform norm of a local cylinder, defined intrinsically from its global
realization. -/
noncomputable def uniformNorm (O : LocalCylinderAlgebra) : ℝ :=
  sSup (Set.range fun sigma => |realizeGlobal O sigma|)

theorem abs_realizeGlobal_le_uniformNorm (O : LocalCylinderAlgebra)
    (sigma : InfiniteIsingConfig) :
    |realizeGlobal O sigma| ≤ uniformNorm O := by
  exact le_csSup (bddAbove_abs_realizeGlobal O) ⟨sigma, rfl⟩

theorem uniformNorm_nonneg (O : LocalCylinderAlgebra) :
    0 ≤ uniformNorm O := by
  exact (abs_nonneg (realizeGlobal O (fun _ => 0))).trans
    (abs_realizeGlobal_le_uniformNorm O (fun _ => 0))

theorem uniformNorm_const (c : ℝ) : uniformNorm (const c) = |c| := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
    · rintro y ⟨sigma, rfl⟩
      rfl
  · exact le_csSup (bddAbove_abs_realizeGlobal (const c))
      ⟨(fun _ => 0), rfl⟩

theorem uniformNorm_translate (z : IsingSite) (O : LocalCylinderAlgebra) :
    uniformNorm (z +ᵥ O) = uniformNorm O := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
    · rintro y ⟨sigma, rfl⟩
      change |realizeGlobal (z +ᵥ O) sigma| ≤ uniformNorm O
      calc
        |realizeGlobal (z +ᵥ O) sigma| =
            |realizeGlobal O (fun q => sigma (q + z))| :=
          congrArg abs (congrFun (realizeGlobal_translate z O) sigma)
        _ ≤ uniformNorm O := abs_realizeGlobal_le_uniformNorm O _
  · apply csSup_le
    · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
    · rintro y ⟨sigma, rfl⟩
      let eta : InfiniteIsingConfig := fun q => sigma (q - z)
      have hrecover : (fun q => eta (q + z)) = sigma := by
        funext q
        simp [eta]
      have hpoint := abs_realizeGlobal_le_uniformNorm (z +ᵥ O) eta
      change |realizeGlobal (z +ᵥ O) eta| ≤ uniformNorm (z +ᵥ O) at hpoint
      calc
        |realizeGlobal O sigma| = |realizeGlobal O (fun q => eta (q + z))| := by
          rw [hrecover]
        _ = |realizeGlobal (z +ᵥ O) eta| :=
          congrArg abs (congrFun (realizeGlobal_translate z O) eta).symm
        _ ≤ uniformNorm (z +ᵥ O) := hpoint

/-! ## Contractivity of the infinite-volume state -/

theorem infiniteStateValue_const
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (c : ℝ) :
    infiniteStateValue beta gamma alpha halpha0 halpha1 hwin (const c) = c := by
  have hc : const c = c • (1 : LocalCylinderAlgebra) := by
    apply realizeGlobal_injective
    funext sigma
    calc
      realizeGlobal (const c) sigma = c :=
        congrFun (LocalCylinderAlgebra.realizeGlobal_const c) sigma
      _ = c * 1 := (mul_one c).symm
      _ = realizeGlobal (c • (1 : LocalCylinderAlgebra)) sigma := by
        rw [congrFun (realizeGlobal_smul c 1) sigma]
        rfl
  rw [hc, infiniteStateValue_smul, infiniteStateValue_one, mul_one]

theorem infiniteStateValue_neg
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O : LocalCylinderAlgebra) :
    infiniteStateValue beta gamma alpha halpha0 halpha1 hwin (-O) =
      -infiniteStateValue beta gamma alpha halpha0 halpha1 hwin O := by
  have hneg : -O = (-1 : ℝ) • O := by
    apply realizeGlobal_injective
    funext sigma
    calc
      realizeGlobal (-O) sigma = -realizeGlobal O sigma :=
        congrFun (realizeGlobal_neg O) sigma
      _ = (-1 : ℝ) * realizeGlobal O sigma := by ring
      _ = realizeGlobal ((-1 : ℝ) • O) sigma :=
        (congrFun (realizeGlobal_smul (-1) O) sigma).symm
  rw [hneg, infiniteStateValue_smul]
  ring

/-- **Uniform contractivity.**  Positivity and normalization force the
infinite-volume value to have operator norm at most one for the intrinsic
uniform norm. -/
theorem abs_infiniteStateValue_le_uniformNorm
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O : LocalCylinderAlgebra) :
    |infiniteStateValue beta gamma alpha halpha0 halpha1 hwin O| ≤
      uniformNorm O := by
  let M := uniformNorm O
  have hminus : 0 ≤ infiniteStateValue beta gamma alpha halpha0 halpha1 hwin
      (const M + -O) := by
    apply infiniteStateValue_nonneg
    intro sigma
    have hreal : realizeGlobal (const M + -O) sigma = M - realizeGlobal O sigma := by
      calc
        realizeGlobal (const M + -O) sigma =
            realizeGlobal (const M) sigma + realizeGlobal (-O) sigma :=
          congrFun (realizeGlobal_add (const M) (-O)) sigma
        _ = M + -realizeGlobal O sigma := by
          rw [congrFun (LocalCylinderAlgebra.realizeGlobal_const M) sigma]
          exact congrArg (M + ·) (congrFun (realizeGlobal_neg O) sigma)
        _ = M - realizeGlobal O sigma := rfl
    rw [hreal]
    have h := abs_realizeGlobal_le_uniformNorm O sigma
    dsimp [M] at h ⊢
    exact sub_nonneg.mpr (le_trans (le_abs_self _) h)
  have hplus : 0 ≤ infiniteStateValue beta gamma alpha halpha0 halpha1 hwin
      (const M + O) := by
    apply infiniteStateValue_nonneg
    intro sigma
    have hreal : realizeGlobal (const M + O) sigma = M + realizeGlobal O sigma := by
      calc
        realizeGlobal (const M + O) sigma =
            realizeGlobal (const M) sigma + realizeGlobal O sigma :=
          congrFun (realizeGlobal_add (const M) O) sigma
        _ = M + realizeGlobal O sigma := by
          rw [congrFun (LocalCylinderAlgebra.realizeGlobal_const M) sigma]
    rw [hreal]
    have h := abs_realizeGlobal_le_uniformNorm O sigma
    dsimp [M] at h ⊢
    linarith [le_trans (neg_le_abs _) h]
  rw [infiniteStateValue_add, infiniteStateValue_const,
    infiniteStateValue_neg] at hminus
  rw [infiniteStateValue_add, infiniteStateValue_const] at hplus
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The terminal D-8 state is contractive for the intrinsic uniform norm. -/
theorem TranslationInvariantSiteCylinderState.contractive
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O : LocalCylinderAlgebra) :
    |infiniteTranslationInvariantSiteCylinderState
        beta gamma alpha halpha0 halpha1 hwin O| ≤ uniformNorm O :=
  abs_infiniteStateValue_le_uniformNorm
    beta gamma alpha halpha0 halpha1 hwin O

end LocalCylinderAlgebra
end Dobrushin
end YangMills.OS
