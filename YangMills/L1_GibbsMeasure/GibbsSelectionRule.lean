/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.SUNSelectionRule

/-!
# Centre symmetry of the Wilson action and the interacting selection rule

The lattice Wilson action has an exact **centre symmetry**: every plaquette
traverses two positively- and two negatively-oriented edges (the concrete
geometry's signs are `(+,+,−,−)`), so under the centre action each plaquette
holonomy picks up `z·z·z⁻¹·z⁻¹ = 1` — the holonomy is *invariant*, for any
central `z` and **any** plaquette energy.  Hence the Gibbs (interacting)
measure is centre-invariant, and the Z_N selection rule holds for the **full
interacting SU(n) lattice gauge theory at every coupling β**:

  `∫ W_es d(gibbsMeasure (sunHaarProb n) pe β) = 0`  whenever `n ∤ L`.

Chain: `centerAct_apply_neg` (the action on reversed edges, by centrality) →
`plaquetteHolonomy_centerAct` (plaquette invariance, via the four-factor
centre identity) → `wilsonAction_centerAct` → `integral_centerAct_gibbs`
(tilted-measure transport, `integral_tilted`) → the headline.

All statements are finite-volume, lattice, M3-side; nothing here concerns
M4/M5/Clay (`docs/DEPENDENCY-GRAPH.md` §2).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory GaugeConfig

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-- Four-factor centre identity: `(za)(zb)(z⁻¹c)(z⁻¹e) = abce` for central
`z`. -/
private lemma central_four (z : G) (hz : ∀ y : G, Commute z y)
    (a b c e : G) :
    (z * a) * (z * b) * (z⁻¹ * c) * (z⁻¹ * e) = a * b * c * e := by
  have hzi : ∀ y : G, Commute z⁻¹ y := fun y => (hz y).inv_left
  have hcomm : Commute (a * b) (z⁻¹ * z⁻¹) :=
    ((hzi (a * b)).symm).mul_right ((hzi (a * b)).symm)
  calc (z * a) * (z * b) * (z⁻¹ * c) * (z⁻¹ * e)
      = ((z * a) * (z * b)) * ((z⁻¹ * c) * (z⁻¹ * e)) := by
        rw [mul_assoc ((z * a) * (z * b))]
    _ = ((z * z) * (a * b)) * ((z⁻¹ * z⁻¹) * (c * e)) := by
        rw [Commute.mul_mul_mul_comm ((hz a).symm),
          Commute.mul_mul_mul_comm ((hzi c).symm)]
    _ = ((z * z) * (z⁻¹ * z⁻¹)) * ((a * b) * (c * e)) :=
        Commute.mul_mul_mul_comm hcomm _ _
    _ = a * b * c * e := by
        have hzz : (z * z) * (z⁻¹ * z⁻¹) = 1 := by group
        rw [hzz, one_mul, ← mul_assoc]

/-- On negatively-oriented edges, the centre action by a central `z` is left
multiplication by `z⁻¹` (through the reversal constraint). -/
lemma centerAct_apply_neg (z : G) (hz : ∀ y : G, Commute z y)
    (A : GaugeConfig d N G) (e : ConcreteEdge d N) (he : e.sign = false) :
    centerAct z A e = z⁻¹ * A e := by
  show posToFun (fun e' => z * configToPos A e') e = z⁻¹ * A e
  unfold posToFun
  rw [dif_neg (by simp [he])]
  have hrev : A { e with sign := true } = (A e)⁻¹ := by
    have hmr := A.map_reverse e
    rw [finBoxGeometry_reverse] at hmr
    simpa [he] using hmr
  show (z * A { e with sign := true })⁻¹ = z⁻¹ * A e
  rw [hrev, mul_inv_rev, inv_inv]
  exact ((hz (A e)).inv_left.eq).symm

/-- **Centre symmetry of the plaquette holonomy:** every plaquette traverses
two positive and two negative edges, so the centre factors cancel exactly. -/
lemma plaquetteHolonomy_centerAct (z : G) (hz : ∀ y : G, Commute z y)
    (A : GaugeConfig d N G)
    (p : FiniteLatticeGeometry.P (d := d) (N := N) (G := G)) :
    plaquetteHolonomy (centerAct z A) p = plaquetteHolonomy A p := by
  have h0 := centerAct_apply_pos z A
    (FiniteLatticeGeometry.plaquetteEdge (d := d) (N := N) (G := G) p 0) rfl
  have h1 := centerAct_apply_pos z A
    (FiniteLatticeGeometry.plaquetteEdge (d := d) (N := N) (G := G) p 1) rfl
  have h2 := centerAct_apply_neg z hz A
    (FiniteLatticeGeometry.plaquetteEdge (d := d) (N := N) (G := G) p 2) rfl
  have h3 := centerAct_apply_neg z hz A
    (FiniteLatticeGeometry.plaquetteEdge (d := d) (N := N) (G := G) p 3) rfl
  unfold plaquetteHolonomy
  rw [h0, h1, h2, h3]
  exact central_four z hz _ _ _ _

/-- **Centre symmetry of the Wilson action** (any plaquette energy). -/
theorem wilsonAction_centerAct (pe : G → ℝ) (z : G)
    (hz : ∀ y : G, Commute z y) (A : GaugeConfig d N G) :
    wilsonAction pe (centerAct z A) = wilsonAction pe A := by
  unfold wilsonAction
  exact Finset.sum_congr rfl fun p _ => by
    rw [plaquetteHolonomy_centerAct z hz A p]

/-- **The interacting (Gibbs) measure is centre-invariant:** the centre
action preserves both the free gauge measure and the Boltzmann weight, hence
every Gibbs expectation. -/
theorem integral_centerAct_gibbs (μ : Measure G) [IsProbabilityMeasure μ]
    [MeasurableMul G] [μ.IsMulLeftInvariant]
    (pe : G → ℝ) (β : ℝ) (z : G) (hz : ∀ y : G, Commute z y)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : GaugeConfig d N G → E') :
    ∫ A, f (centerAct z A) ∂(gibbsMeasure (d := d) (N := N) μ pe β)
      = ∫ A, f A ∂(gibbsMeasure (d := d) (N := N) μ pe β) := by
  unfold gibbsMeasure
  rw [MeasureTheory.integral_tilted, MeasureTheory.integral_tilted]
  have hgoal := integral_centerAct (d := d) (N := N) μ z
    (fun B => (Real.exp (-β * wilsonAction pe B) /
      ∫ x, Real.exp (-β * wilsonAction pe x)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) • f B)
  simp only [wilsonAction_centerAct pe z hz] at hgoal
  exact hgoal

/-- **The Z_n selection rule for the interacting SU(n) lattice gauge theory.**
For the Gibbs measure at **any** coupling `β` and **any** plaquette energy,
the expectation of a positively-oriented Wilson loop whose length is not
divisible by `n` vanishes:
`∫ W_es d(gibbsMeasure (sunHaarProb n) pe β) = 0` for `n ∤ L`.

Every ingredient is machine-checked: Haar left-invariance of `sunHaarProb`,
the exact centre symmetry of the Wilson action (plaquettes have net centre
charge zero), the tilted-measure transport, the centre eigenvalue `ω^L` of
the loop, and `ω^L ≠ 1` for `n ∤ L`.  Finite-volume lattice statement
(M3-side). -/
theorem integral_wilsonLoopSU_gibbs_eq_zero {n : ℕ} [NeZero n]
    (pe : ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) → ℝ) (β : ℝ)
    (es : List (ConcreteEdge d N)) (hpos : ∀ e ∈ es, e.sign = true)
    (hL : ¬ n ∣ es.length) :
    ∫ A, wilsonLoopSU A es
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) = 0 := by
  have hpt : ∀ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es
      = rootOfUnity n ^ es.length * wilsonLoopSU A es :=
    fun A => wilsonLoopSU_centerAct A es hpos
  have hinv : ∫ A, wilsonLoopSU A es
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)
      = ∫ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) :=
    (integral_centerAct_gibbs (sunHaarProb n) pe β (scalarCenterElement n)
      (scalarCenterElement_commute n) _).symm
  have hmul : ∫ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)
      = rootOfUnity n ^ es.length * ∫ A, wilsonLoopSU A es
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) := by
    rw [show (fun A => wilsonLoopSU (centerAct (scalarCenterElement n) A) es)
        = fun A => rootOfUnity n ^ es.length * wilsonLoopSU A es from
      funext hpt]
    exact MeasureTheory.integral_const_mul _ _
  rw [hmul] at hinv
  have hfactor : (1 - rootOfUnity n ^ es.length) *
      ∫ A, wilsonLoopSU A es
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) = 0 := by
    linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm
      (rootOfUnity_pow_ne_one_of_not_dvd n es.length hL)
  · exact h2

/-- **The correlator selection rule:** the Gibbs expectation of a *product*
of two Wilson loops vanishes unless their **total** length is divisible by
`n` — the `Z_n` charge of a correlator is the sum of its loops' N-alities.
(In particular `⟨W_L · W_{L'}⟩ = 0` whenever `n ∤ L + L'`, at any coupling.)
This is the symmetry constraint on the two-loop correlators that
mass-gap/clustering statements are about. -/
theorem integral_wilsonLoopSU_mul_gibbs_eq_zero {n : ℕ} [NeZero n]
    (pe : ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) → ℝ) (β : ℝ)
    (es es' : List (ConcreteEdge d N))
    (hpos : ∀ e ∈ es, e.sign = true) (hpos' : ∀ e ∈ es', e.sign = true)
    (hL : ¬ n ∣ (es.length + es'.length)) :
    ∫ A, wilsonLoopSU A es * wilsonLoopSU A es'
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) = 0 := by
  have hpt : ∀ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es *
        wilsonLoopSU (centerAct (scalarCenterElement n) A) es'
      = rootOfUnity n ^ (es.length + es'.length) *
        (wilsonLoopSU A es * wilsonLoopSU A es') := by
    intro A
    rw [wilsonLoopSU_centerAct A es hpos, wilsonLoopSU_centerAct A es' hpos',
      pow_add]
    ring
  have hinv : ∫ A, wilsonLoopSU A es * wilsonLoopSU A es'
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)
      = ∫ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es *
          wilsonLoopSU (centerAct (scalarCenterElement n) A) es'
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) :=
    (integral_centerAct_gibbs (sunHaarProb n) pe β (scalarCenterElement n)
      (scalarCenterElement_commute n)
      (fun A => wilsonLoopSU A es * wilsonLoopSU A es')).symm
  have hmul : ∫ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es *
        wilsonLoopSU (centerAct (scalarCenterElement n) A) es'
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)
      = rootOfUnity n ^ (es.length + es'.length) *
        ∫ A, wilsonLoopSU A es * wilsonLoopSU A es'
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) := by
    rw [show (fun A => wilsonLoopSU (centerAct (scalarCenterElement n) A) es *
        wilsonLoopSU (centerAct (scalarCenterElement n) A) es')
        = fun A => rootOfUnity n ^ (es.length + es'.length) *
          (wilsonLoopSU A es * wilsonLoopSU A es') from funext hpt]
    exact MeasureTheory.integral_const_mul _ _
  rw [hmul] at hinv
  have hfactor : (1 - rootOfUnity n ^ (es.length + es'.length)) *
      ∫ A, wilsonLoopSU A es * wilsonLoopSU A es'
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) = 0 := by
    linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm
      (rootOfUnity_pow_ne_one_of_not_dvd n _ hL)
  · exact h2

/-- **Connected correlator selection rule:** the charged two-loop connected
expression vanishes under the interacting Gibbs measure whenever the total
centre charge is non-trivial.

This packages the two existing symmetry consequences: the product expectation
vanishes by the total-charge selection rule, while at least one of the two
single-loop expectations vanishes because `n ∤ (L + L')` forbids both `L` and
`L'` from being divisible by `n`. -/
theorem connected_wilsonLoopSU_gibbs_eq_zero {n : ℕ} [NeZero n]
    (pe : ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) → ℝ) (β : ℝ)
    (es es' : List (ConcreteEdge d N))
    (hpos : ∀ e ∈ es, e.sign = true) (hpos' : ∀ e ∈ es', e.sign = true)
    (hL : ¬ n ∣ (es.length + es'.length)) :
    (∫ A, wilsonLoopSU A es * wilsonLoopSU A es'
        ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β))
      - (∫ A, wilsonLoopSU A es
          ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)) *
        (∫ A, wilsonLoopSU A es'
          ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)) = 0 := by
  have hprod := integral_wilsonLoopSU_mul_gibbs_eq_zero
    (d := d) (N := N) pe β es es' hpos hpos' hL
  have hmeans :
      (∫ A, wilsonLoopSU A es
          ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)) *
        (∫ A, wilsonLoopSU A es'
          ∂(gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β)) = 0 := by
    by_cases hdiv : n ∣ es.length
    · have hdiv' : ¬ n ∣ es'.length := by
        intro hdiv'
        exact hL (Nat.dvd_add hdiv hdiv')
      have hright := integral_wilsonLoopSU_gibbs_eq_zero
        (d := d) (N := N) pe β es' hpos' hdiv'
      rw [hright, mul_zero]
    · have hleft := integral_wilsonLoopSU_gibbs_eq_zero
        (d := d) (N := N) pe β es hpos hdiv
      rw [hleft, zero_mul]
  rw [hprod, hmeans, sub_zero]

end YangMills
