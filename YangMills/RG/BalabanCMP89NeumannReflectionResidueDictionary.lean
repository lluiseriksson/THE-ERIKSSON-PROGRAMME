import YangMills.RG.BalabanCMP89NeumannReflectionScaleDictionary

/-!
# CMP89 (2.42): rectangular reflection residues

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this module is compiler-verified.

For a half-open source rectangle `0 <= x_mu,n_mu < m_mu`, the two branches of
the multiple-reflection expansion have exact displacements

`x_mu - (2*k_mu*m_mu + n_mu) = (x_mu-n_mu) + 2*m_mu*(-k_mu)`

and

`x_mu - (2*k_mu*m_mu - n_mu - 1) = (x_mu+n_mu+1) + 2*m_mu*(-k_mu)`.

Thus the rectangular period is coordinatewise `2*m_mu`.  The reflected base
residue has two centered magnitudes, `x_mu+n_mu+1` and
`2*m_mu-x_mu-n_mu-1`; both dominate `|x_mu-n_mu|`.  This is the exact static
bridge needed before reindexing the image series into centered periodic
fibres.  It does not assert the Green representation, summability, or a
regional decay estimate.
-/

namespace YangMills.RG

/-- Base residue of one reflection branch before its period translation. -/
def cmp89NeumannReflectionBaseResidue {d : ℕ}
    (x n : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d) :
    Fin d → ℤ :=
  fun mu => if branch mu then x mu + n mu + 1 else x mu - n mu

/-- The source rectangle has coordinatewise reflection period `2*m_mu`. -/
def cmp89NeumannReflectionPeriod {d : ℕ} (m : Fin d → ℤ) :
    Fin d → ℤ :=
  fun mu => 2 * m mu

/-- Exact coordinatewise decomposition of a reflected displacement into its
base residue and an integer multiple of the rectangular period. -/
theorem cmp89NeumannReflection_displacement_apply
    {d : ℕ} (m x n k : Fin d → ℤ)
    (branch : CMP89NeumannReflectionBranch d) (mu : Fin d) :
    x mu - cmp89NeumannReflectionImage m n k branch mu =
      cmp89NeumannReflectionBaseResidue x n branch mu +
        cmp89NeumannReflectionPeriod m mu * (-k mu) := by
  cases hbranch : branch mu <;>
    simp [cmp89NeumannReflectionImage, cmp89NeumannReflectionOrbit,
      cmp89NeumannReflectionBaseResidue, cmp89NeumannReflectionPeriod,
      hbranch] <;> ring

/-- Vector form of the exact rectangular residue decomposition. -/
theorem cmp89NeumannReflection_displacement
    {d : ℕ} (m x n k : Fin d → ℤ)
    (branch : CMP89NeumannReflectionBranch d) :
    x - cmp89NeumannReflectionImage m n k branch =
      cmp89NeumannReflectionBaseResidue x n branch +
        fun mu => cmp89NeumannReflectionPeriod m mu * (-k mu) := by
  funext mu
  exact cmp89NeumannReflection_displacement_apply m x n k branch mu

/-- The centered magnitude of the reflected base residue.  The two entries
are the distances of `x+n+1` from the two ends of a period of length `2*m`.
-/
def cmp89NeumannReflectedCenteredMagnitude (m x n : ℤ) : ℤ :=
  min (x + n + 1) (2 * m - x - n - 1)

/-- Both centered reflected distances dominate the direct distance inside
the half-open source carrier. -/
theorem cmp89Neumann_direct_natAbs_le_reflected_distances
    {m x n : ℤ} (hx : 0 ≤ x ∧ x < m) (hn : 0 ≤ n ∧ n < m) :
    ((x - n).natAbs : ℤ) ≤ x + n + 1 ∧
      ((x - n).natAbs : ℤ) ≤ 2 * m - x - n - 1 := by
  by_cases hxn : x ≤ n
  · have hnonpos : x - n ≤ 0 := by omega
    rw [Int.ofNat_natAbs_of_nonpos hnonpos]
    constructor <;> omega
  · have hnonneg : 0 ≤ x - n := by omega
    rw [Int.natAbs_of_nonneg hnonneg]
    constructor <;> omega

/-- Centering the reflected branch modulo `2*m` does not weaken the direct
source-site separation. -/
theorem cmp89Neumann_direct_natAbs_le_reflectedCenteredMagnitude
    {m x n : ℤ} (hx : 0 ≤ x ∧ x < m) (hn : 0 ≤ n ∧ n < m) :
    ((x - n).natAbs : ℤ) ≤
      cmp89NeumannReflectedCenteredMagnitude m x n := by
  rw [cmp89NeumannReflectedCenteredMagnitude]
  exact le_min_iff.mpr
    (cmp89Neumann_direct_natAbs_le_reflected_distances hx hn)

/-- Coordinatewise rectangular version consumed by the later product
exponential estimate. -/
theorem cmp89Neumann_direct_natAbs_le_reflectedCenteredMagnitude_apply
    {d : ℕ} {m x n : Fin d → ℤ}
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (mu : Fin d) :
    ((x mu - n mu).natAbs : ℤ) ≤
      cmp89NeumannReflectedCenteredMagnitude (m mu) (x mu) (n mu) :=
  cmp89Neumann_direct_natAbs_le_reflectedCenteredMagnitude
    (hx mu) (hn mu)

end YangMills.RG
