import YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary

/-!
# PRE-VALIDATION: arbitrary finite-grid residue classes as centered affine fibres

The finite-grid selector returns an arbitrary residue class, not only residue
zero.  This draft fixes the coordinatewise `ZMod.valMinAbs` representative,
translates the arbitrary class to the already sealed zero class, and then
reuses the centered-periodic reindexing.  At an even antipodal residue the
signed representative is deliberately the `valMinAbs` choice; only the
existing magnitude theorem is used downstream.

No physical Green identity, regional `B0`/`delta0`, window-15 attainment,
terminal field, counter movement or `TermSource` inhabitant is asserted.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Coordinatewise canonical integer representative of a finite-grid
residue.  The convention is explicit because the even antipodal residue has
two shortest signed representatives. -/
def cmp99FlatIntegerResidueRepresentative
    {d N : ℕ} [NeZero N] (r : CMP99FlatZModBox d N) : Fin d → ℤ :=
  fun mu ↦ (r mu).valMinAbs

/-- The canonical integer representative projects to the literal residue. -/
@[simp] theorem cmp99FlatIntegerResidue_representative
    {d N : ℕ} [NeZero N] (r : CMP99FlatZModBox d N) :
    cmp99FlatIntegerResidue (N := N)
        (cmp99FlatIntegerResidueRepresentative r) = r := by
  funext mu
  exact ZMod.coe_valMinAbs (r mu)

/-- Translation by the canonical representative identifies residue zero
with an arbitrary residue class. -/
def cmp99FlatIntegerResidueClassTranslationEquiv
    (d N : ℕ) [NeZero N] (r : CMP99FlatZModBox d N) :
    CMP99FlatIntegerResidueClass d N 0 ≃
      CMP99FlatIntegerResidueClass d N r where
  toFun n := ⟨cmp99FlatIntegerResidueRepresentative r + n.1, by
    funext mu
    have hn := congrFun n.property mu
    change
      (((cmp99FlatIntegerResidueRepresentative r mu + n.1 mu : ℤ) :
          ZMod N)) = r mu
    rw [Int.cast_add, hn]
    simp⟩
  invFun n := ⟨n.1 - cmp99FlatIntegerResidueRepresentative r, by
    funext mu
    have hn := congrFun n.property mu
    change
      (((n.1 mu - cmp99FlatIntegerResidueRepresentative r mu : ℤ) :
          ZMod N)) = 0
    rw [Int.cast_sub, hn]
    simp⟩
  left_inv n := by
    apply Subtype.ext
    funext mu
    simp
  right_inv n := by
    apply Subtype.ext
    funext mu
    simp

/-- Exact equivalence between `Z^d` and any selected finite-grid residue
class.  It is the sealed zero-residue equivalence followed by translation;
no enumeration or cardinality argument enters. -/
def cmp99FlatIntegerResidueClassEquiv
    (d N : ℕ) [NeZero N] (r : CMP99FlatZModBox d N) :
    (Fin d → ℤ) ≃ CMP99FlatIntegerResidueClass d N r :=
  (cmp99FlatIntegerZeroResidueClassEquiv d N).trans
    (cmp99FlatIntegerResidueClassTranslationEquiv d N r)

/-- Evaluation of the arbitrary-residue equivalence exposes the literal
affine fibre `representative + N*m`. -/
@[simp] theorem cmp99FlatIntegerResidueClassEquiv_apply_coe
    {d N : ℕ} [NeZero N] (r : CMP99FlatZModBox d N)
    (m : Fin d → ℤ) :
    (cmp99FlatIntegerResidueClassEquiv d N r m).1 =
      fun mu ↦ cmp99FlatIntegerResidueRepresentative r mu + (N : ℤ) * m mu := by
  funext mu
  simp [cmp99FlatIntegerResidueClassEquiv,
    cmp99FlatIntegerResidueClassTranslationEquiv,
    cmp99FlatIntegerZeroResidueClassEquiv]

/-- Reindex an arbitrary residue-class sum by its exact affine fibre. -/
theorem tsum_cmp99FlatIntegerResidueClass_eq_affine
    {d N : ℕ} [NeZero N] (r : CMP99FlatZModBox d N)
    (f : (Fin d → ℤ) → ℝ) :
    (∑' n : CMP99FlatIntegerResidueClass d N r, f n.1) =
      ∑' m : Fin d → ℤ,
        f (fun mu ↦
          cmp99FlatIntegerResidueRepresentative r mu + (N : ℤ) * m mu) := by
  let e := cmp99FlatIntegerResidueClassEquiv d N r
  rw [← e.tsum_eq]
  apply tsum_congr
  intro m
  congr 1
  exact cmp99FlatIntegerResidueClassEquiv_apply_coe r m

/-- After an outer affine scale `K`, an arbitrary selected residue class is
exactly one centered fibre of full physical period `K*N`. -/
theorem tsum_cmp99FlatIntegerResidueClass_eq_centeredPeriodic
    {d K N : ℕ} [NeZero K] [NeZero N]
    (r : CMP99FlatZModBox d N) (u : Fin d → ℤ)
    (f : (Fin d → ℤ) → ℝ) :
    (∑' n : CMP99FlatIntegerResidueClass d N r,
        f (fun mu ↦ u mu + (K : ℤ) * n.1 mu)) =
      ∑' m : Fin d → ℤ,
        f (fun mu ↦
          cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
              (fun nu ↦ u nu + (K : ℤ) *
                cmp99FlatIntegerResidueRepresentative r nu) mu +
            ((K * N : ℕ) : ℤ) * m mu) := by
  have hKN : NeZero (K * N) :=
    ⟨Nat.mul_ne_zero (NeZero.ne K) (NeZero.ne N)⟩
  letI : NeZero (K * N) := hKN
  rw [tsum_cmp99FlatIntegerResidueClass_eq_affine r
    (fun v ↦ f (fun mu ↦ u mu + (K : ℤ) * v mu))]
  have hscale :
      (∑' m : Fin d → ℤ,
          f (fun mu ↦ u mu + (K : ℤ) *
            (cmp99FlatIntegerResidueRepresentative r mu + (N : ℤ) * m mu))) =
        ∑' m : Fin d → ℤ,
          f (fun mu ↦
            (u mu + (K : ℤ) * cmp99FlatIntegerResidueRepresentative r mu) +
              ((K * N : ℕ) : ℤ) * m mu) := by
    apply tsum_congr
    intro m
    congr 1
    funext mu
    push_cast
    ring
  rw [hscale]
  exact tsum_cmp99CenteredPeriodicEndpoint_reindex (K * N)
    (fun mu ↦ u mu + (K : ℤ) * cmp99FlatIntegerResidueRepresentative r mu)
    f

/-- Generic norm bound for an arbitrary selected residue class.  The only
new datum relative to the sealed zero-residue theorem is the displayed
canonical representative inside the physical-period centering. -/
theorem tsum_norm_cmp99FlatIntegerResidueClass_le_centeredPeriodic
    {d K N : ℕ} [NeZero K] [NeZero N]
    {rho A : ℝ} (hrho : 0 < rho) (hA : 0 ≤ A)
    (coefficient : (Fin d → ℤ) → ℂ)
    (hcoefficient : ∀ v,
      ‖coefficient v‖ ≤ A *
        cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ)) v)
    (r : CMP99FlatZModBox d N) (u : Fin d → ℤ) :
    (∑' n : CMP99FlatIntegerResidueClass d N r,
        ‖coefficient (fun mu ↦ u mu + (K : ℤ) * n.1 mu)‖) ≤
      A *
        ((2 / (1 - Real.exp (-rho))) ^ d *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
              (fun mu ↦ u mu + (K : ℤ) *
                cmp99FlatIntegerResidueRepresentative r mu))) := by
  have hKN : NeZero (K * N) :=
    ⟨Nat.mul_ne_zero (NeZero.ne K) (NeZero.ne N)⟩
  letI : NeZero (K * N) := hKN
  rw [tsum_cmp99FlatIntegerResidueClass_eq_centeredPeriodic r u
    (fun v ↦ ‖coefficient v‖)]
  have hzero :=
    tsum_norm_cmp99FlatIntegerZeroResidueClass_le_centeredPeriodic
      (K := K) (N := N) hrho hA coefficient hcoefficient
      (fun mu ↦ u mu + (K : ℤ) *
        cmp99FlatIntegerResidueRepresentative r mu)
  rw [tsum_cmp99FlatIntegerZeroResidueClass_eq_centeredPeriodic
    (K := K) (N := N)
    (fun mu ↦ u mu + (K : ℤ) *
      cmp99FlatIntegerResidueRepresentative r mu)
    (fun v ↦ ‖coefficient v‖)] at hzero
  exact hzero

end

end YangMills.RG
