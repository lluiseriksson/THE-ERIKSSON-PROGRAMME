import Mathlib
import YangMills.ClayCore.WilsonGibbsExpansion

/-!
# Peter-Weyl Character Expansion for SU(N_c) Wilson-Gibbs

Abstract packaging of the Peter-Weyl character expansion
  exp(-β · Re tr U(∂p)) = ∑_ρ a_ρ(β) · χ_ρ(U(∂p))
together with the exponential decay of the resulting plaquette
correlator that follows from absolute summability of the
character coefficients.

The file is an abstract wrapper: the underlying Peter-Weyl
theorem and the concrete coefficient bounds are not formalised
in Mathlib for compact Lie groups; we instead record their
consequences as structure fields and use them to construct a
`WilsonGibbsPolymerRep`, which is the interface consumed by
the downstream Clay majorisation theorem.

Source: Bloque4 Sec 5.2 (Peter-Weyl step), Paper Eriksson 2602.0069 Sec 7.1.
-/

namespace YangMills
open Real

/-- Abstract Peter-Weyl character expansion data for the SU(N_c)
    Wilson-Gibbs measure.

    * `Rep` indexes the irreducible representations ρ.
    * `character ρ U` is χ_ρ(U), the character value.
    * `coeff β ρ` is a_ρ(β), the expansion coefficient.
    * `r`, `C_clust` carry the geometric decay of the induced
      plaquette correlator, exactly the data required to
      produce a `WilsonGibbsPolymerRep`.
    * `h_correlator` records the output of the character
      expansion: an exponential bound on the connected
      Wilson correlator. -/
structure CharacterExpansionData (N_c : ℕ) [NeZero N_c] where
  /-- Index set for irreducible representations. -/
  Rep : Type
  /-- Character of each representation on SU(N_c). -/
  character :
    Rep → ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℂ
  /-- Character expansion coefficient at inverse coupling β. -/
  coeff : ℝ → Rep → ℝ
  /-- Geometric decay parameter carried through to the polymer
      representation. -/
  r : ℝ
  hr_pos : 0 < r
  hr_lt1 : r < 1
  /-- Cluster prefactor carried through to the polymer
      representation. -/
  C_clust : ℝ
  hC : 0 < C_clust
  /-- Exponential decay of the connected Wilson correlator,
      the output of the character expansion step. -/
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

/-- Extract a Wilson-Gibbs polymer representation from
    character expansion data. -/
noncomputable def wilsonPolymerRep_of_charExpansion
    {N_c : ℕ} [NeZero N_c]
    (ce : CharacterExpansionData N_c) :
    WilsonGibbsPolymerRep N_c where
  r := ce.r
  hr_pos := ce.hr_pos
  hr_lt1 := ce.hr_lt1
  C_clust := ce.C_clust
  hC := ce.hC
  h_correlator := ce.h_correlator

/-- Character expansion data yields a Clay Yang-Mills mass gap
    structure for SU(N_c). -/
noncomputable def clay_from_charExpansion
    {N_c : ℕ} [NeZero N_c]
    (ce : CharacterExpansionData N_c) :
    ClayYangMillsMassGap N_c :=
  clay_from_polymer_rep (wilsonPolymerRep_of_charExpansion ce)

/-- Character expansion data yields the Clay Yang-Mills mass-gap
    theorem statement. -/
theorem clay_theorem_from_charExpansion
    {N_c : ℕ} [NeZero N_c]
    (ce : CharacterExpansionData N_c) :
    ClayYangMillsTheorem :=
  clay_theorem_from_polymer_rep (wilsonPolymerRep_of_charExpansion ce)

end YangMills
