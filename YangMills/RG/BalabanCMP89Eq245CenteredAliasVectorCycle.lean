/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245CenteredAliasCycle

/-!
# PRE-VALIDATION: centered CMP89 alias-vector cycle

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

CMP89 (2.45) sums over a Cartesian product of centered reciprocal-alias
fibres.  The scalar cycle is already cold-sealed.  This module lifts it to a
permutation of the full alias-vector fibre by cycling exactly one coordinate.

The lift is constructed through an explicit equivalence between membership in
the `piFinset` and a dependent product of scalar subtypes.  Consequently the
final sum-reindexing theorem uses an actual permutation of the printed finite
fibre; it does not assume pointwise `2*pi` periodicity of an individual alias
term.  The coordinate theorem retains the literal wrap by `N`, which is the
input needed later for the already sealed `2*pi*N` phase periodicity.

No periodicity of the complete CMP89 integrand is claimed here.  In
particular, the central/noncentral split of the stabilized integrand is not
preserved pointwise by this cycle.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Membership of an alias vector in the printed Cartesian fibre gives
membership of each coordinate in the scalar centered fibre. -/
theorem cmp89Eq245CenteredAliasVector_coordinate_mem
    (d N : ℕ)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N})
    (mu : Fin d) :
    m.1 mu ∈ cmp89Eq245CenteredAliasIntegers N := by
  have hm := m.property
  rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
  exact hm mu

/-- The printed centered alias-vector fibre is the dependent product of its
scalar coordinate fibres. -/
def cmp89Eq245CenteredAliasVectorPiEquiv (d N : ℕ) :
    {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N} ≃
      ((mu : Fin d) →
        {x : ℤ // x ∈ cmp89Eq245CenteredAliasIntegers N}) where
  toFun m mu :=
    ⟨m.1 mu, cmp89Eq245CenteredAliasVector_coordinate_mem d N m mu⟩
  invFun f :=
    ⟨fun mu => (f mu).1, by
      rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset]
      intro mu
      exact (f mu).property⟩
  left_inv m := by
    apply Subtype.ext
    funext mu
    rfl
  right_inv f := by
    funext mu
    apply Subtype.ext
    rfl

/-- Cycle one coordinate of the dependent product of scalar alias fibres. -/
def cmp89Eq245CenteredAliasPiCoordinateCycle
    (d N : ℕ) (hN : 0 < N) (mu : Fin d) :
    Equiv.Perm ((nu : Fin d) →
      {x : ℤ // x ∈ cmp89Eq245CenteredAliasIntegers N}) :=
  Equiv.piCongrRight fun nu =>
    if nu = mu then
      cmp89Eq245CenteredAliasCycle N hN
    else
      Equiv.refl _

/-- At the selected coordinate, the product cycle is the scalar centered
cycle. -/
@[simp]
theorem cmp89Eq245CenteredAliasPiCoordinateCycle_apply_self
    (d N : ℕ) (hN : 0 < N) (mu : Fin d)
    (m : (nu : Fin d) →
      {x : ℤ // x ∈ cmp89Eq245CenteredAliasIntegers N}) :
    cmp89Eq245CenteredAliasPiCoordinateCycle d N hN mu m mu =
      cmp89Eq245CenteredAliasCycle N hN (m mu) := by
  simp [cmp89Eq245CenteredAliasPiCoordinateCycle]

/-- Every unselected coordinate is fixed by the product cycle. -/
@[simp]
theorem cmp89Eq245CenteredAliasPiCoordinateCycle_apply_of_ne
    (d N : ℕ) (hN : 0 < N) (mu nu : Fin d)
    (hnu : nu ≠ mu)
    (m : (rho : Fin d) →
      {x : ℤ // x ∈ cmp89Eq245CenteredAliasIntegers N}) :
    cmp89Eq245CenteredAliasPiCoordinateCycle d N hN mu m nu = m nu := by
  simp [cmp89Eq245CenteredAliasPiCoordinateCycle, hnu]

/-- The permutation of the printed alias-vector fibre induced by advancing
one selected centered coordinate. -/
def cmp89Eq245CenteredAliasVectorCycle
    (d N : ℕ) (hN : 0 < N) (mu : Fin d) :
    Equiv.Perm
      {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N} :=
  (cmp89Eq245CenteredAliasVectorPiEquiv d N).trans
    ((cmp89Eq245CenteredAliasPiCoordinateCycle d N hN mu).trans
      (cmp89Eq245CenteredAliasVectorPiEquiv d N).symm)

/-- The vector cycle fixes every coordinate other than the selected one. -/
theorem cmp89Eq245CenteredAliasVectorCycle_apply_of_ne
    (d N : ℕ) (hN : 0 < N) (mu nu : Fin d)
    (hnu : nu ≠ mu)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    (cmp89Eq245CenteredAliasVectorCycle d N hN mu m).1 nu = m.1 nu := by
  simp [cmp89Eq245CenteredAliasVectorCycle,
    cmp89Eq245CenteredAliasVectorPiEquiv,
    cmp89Eq245CenteredAliasPiCoordinateCycle_apply_of_ne,
    hnu]

/-- At the selected coordinate the vector cycle advances by one, either
literally or after the explicit wrap by the alias count `N`. -/
theorem cmp89Eq245CenteredAliasVectorCycle_value_or_wrap
    (d N : ℕ) (hN : 0 < N) (mu : Fin d)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    (cmp89Eq245CenteredAliasVectorCycle d N hN mu m).1 mu =
        m.1 mu + 1 ∨
      (cmp89Eq245CenteredAliasVectorCycle d N hN mu m).1 mu + (N : ℤ) =
        m.1 mu + 1 := by
  simpa [cmp89Eq245CenteredAliasVectorCycle,
    cmp89Eq245CenteredAliasVectorPiEquiv] using
    cmp89Eq245CenteredAliasCycle_value_or_wrap N hN
      ((cmp89Eq245CenteredAliasVectorPiEquiv d N m) mu)

/-- Reindex a finite sum over the printed alias-vector fibre by the selected
coordinate cycle.  This is the algebraic sum-permutation needed by the later
physical `2*pi` boundary identity. -/
theorem cmp89Eq245CenteredAliasVectorCycle_sum
    {A : Type*} [AddCommMonoid A]
    (d N : ℕ) (hN : 0 < N) (mu : Fin d)
    (f : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N} → A) :
    ∑ m, f (cmp89Eq245CenteredAliasVectorCycle d N hN mu m) =
      ∑ m, f m := by
  exact Equiv.sum_comp (cmp89Eq245CenteredAliasVectorCycle d N hN mu) f

end

end YangMills.RG
