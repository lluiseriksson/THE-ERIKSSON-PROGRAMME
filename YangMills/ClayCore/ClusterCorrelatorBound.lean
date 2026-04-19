import Mathlib
import YangMills.ClayCore.CharacterExpansion

/-!
# Cluster Correlator Bound (Phase 15h, Layer B1)

Formalises Theorem 7.1 of Bloque4: the connected Wilson
correlator is controlled by the sum over connecting clusters,
yielding an exponential decay bound.

We package the full cluster-expansion theorem as an explicit
named hypothesis `ClusterCorrelatorBound`.  The provable part
of the story — the triangle decomposition of the connected
correlator — is exposed as
`wilsonConnectedCorr_eq_sub` and
`wilsonConnectedCorr_abs_le_triangle`.

Given the cluster bound as input, we construct a concrete
`CharacterExpansionData` and derive the Clay Yang-Mills
mass-gap structure and theorem via the A1 bridge.

Source: Bloque4 Theorem 7.1, Paper Eriksson 2602.0069 Sec 7.2.
-/

namespace YangMills
open Real

/-- Definitional expansion of the connected correlator. -/
theorem wilsonConnectedCorr_eq_sub
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L) :
    wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
    wilsonCorrelation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q -
    wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p *
    wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F q := rfl

/-- Triangle bound on the connected correlator:
    `|corr| ≤ |⟨FG⟩| + |⟨F⟩|·|⟨G⟩|`. -/
theorem wilsonConnectedCorr_abs_le_triangle
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L) :
    |wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| ≤
    |wilsonCorrelation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| +
    |wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p| *
    |wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F q| := by
  rw [wilsonConnectedCorr_eq_sub, ← abs_mul]
  exact abs_sub _ _

/-- **Cluster correlator bound (B1).**
    The content of Theorem 7.1 of Bloque4 in the form consumed
    by `CharacterExpansionData`: the connected Wilson correlator
    decays exponentially in the site distance, with the KP
    parameter `kpParameter r` as the rate and `C_clust` as
    prefactor, uniformly in the inverse coupling β > 0 and
    the unit-bounded test function `F`. -/
def ClusterCorrelatorBound
    (N_c : ℕ) [NeZero N_c] (r C_clust : ℝ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (_hβ : 0 < β)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (_hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L),
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    |wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| ≤
    C_clust * Real.exp (-(kpParameter r) *
        siteLatticeDist p.site q.site)

/-- Inhabit `CharacterExpansionData` from a cluster correlator
    bound.  The `Rep`, `character`, and `coeff` slots are
    filled with trivial Peter-Weyl metadata; the geometric
    decay (r, C_clust) and the exponential correlator bound
    are carried directly from the hypothesis. -/
noncomputable def wilsonCharExpansion
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h : ClusterCorrelatorBound N_c r C_clust) :
    CharacterExpansionData N_c where
  Rep := PUnit
  character := fun _ _ => (0 : ℂ)
  coeff := fun _ _ => (0 : ℝ)
  r := r
  hr_pos := hr_pos
  hr_lt1 := hr_lt1
  C_clust := C_clust
  hC := hC
  h_correlator := h

/-- **FINAL CHAIN.** Given the cluster correlator bound (B1),
    produce the full Clay Yang-Mills mass-gap structure for
    `SU(N_c)` via the A1 Peter-Weyl bridge. -/
noncomputable def clay_massGap_large_beta
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h : ClusterCorrelatorBound N_c r C_clust) :
    ClayYangMillsMassGap N_c :=
  clay_from_charExpansion
    (wilsonCharExpansion N_c r hr_pos hr_lt1 C_clust hC h)

/-- **THE CLAY THEOREM (from B1).** Given the cluster
    correlator bound, the Clay Yang-Mills mass-gap theorem
    statement follows. -/
theorem clay_yangMills_large_beta
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h : ClusterCorrelatorBound N_c r C_clust) :
    ClayYangMillsTheorem :=
  clay_theorem_from_charExpansion
    (wilsonCharExpansion N_c r hr_pos hr_lt1 C_clust hC h)

end YangMills
