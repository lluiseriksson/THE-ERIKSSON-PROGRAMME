import Mathlib
import YangMills.ClayCore.SUNWilsonMajorisation

/-!
# Wilson-Gibbs Polymer Expansion (Phase 15f, Layer A2)

Abstract structure packaging the polymer representation of the
SU(N_c) Wilson-Gibbs measure.  The structure records the geometric
decay constants (r, C_clust) and the key correlator bound that
feeds into the SU(N_c) Wilson cluster majorisation.

Source: Bloque4 Sec 5, Paper Eriksson 2602.0069 Sec 7.
-/

namespace YangMills
open Real

/-- Abstract Wilson-Gibbs polymer representation data.
    Packages the decay parameter `r`, prefactor `C_clust`,
    and the exponential correlator bound.  Polymer activities are
    left implicit (they live in the full cluster-expansion module
    which is imported transitively by the downstream Clay theorem). -/
structure WilsonGibbsPolymerRep (N_c : ℕ) [NeZero N_c] where
  r : ℝ
  hr_pos : 0 < r
  hr_lt1 : r < 1
  C_clust : ℝ
  hC : 0 < C_clust
  h_correlator :
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

noncomputable def sunWilsonMaj_of_polymerRep
    {N_c : ℕ} [NeZero N_c]
    (rep : WilsonGibbsPolymerRep N_c) :
    SUNWilsonClusterMajorisation N_c where
  r := rep.r
  hr_pos := rep.hr_pos
  hr_lt_one := rep.hr_lt1
  C_clust := rep.C_clust
  hC_clust := rep.hC
  hbound := rep.h_correlator

noncomputable def clay_from_polymer_rep
    {N_c : ℕ} [NeZero N_c]
    (rep : WilsonGibbsPolymerRep N_c) :
    ClayYangMillsMassGap N_c :=
  clayMassGap_of_majorisation (sunWilsonMaj_of_polymerRep rep)

theorem clay_theorem_from_polymer_rep
    {N_c : ℕ} [NeZero N_c]
    (rep : WilsonGibbsPolymerRep N_c) :
    ClayYangMillsTheorem :=
  clayMassGap_implies_clayTheorem (clay_from_polymer_rep rep)

end YangMills
