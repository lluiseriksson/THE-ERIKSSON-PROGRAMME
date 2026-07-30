/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.Expectation
import YangMills.L1_GibbsMeasure.ConnectedEntropy
import YangMills.L1_GibbsMeasure.PolymerExpansion
import YangMills.L1_GibbsMeasure.SupportFactorization

/-!
# Local-observable substrate for thermodynamic-limit work

The finite lattice in this repository is a torus: the side length is a type
index in `GaugeConfig d N G`, and there is no boundary-condition object.
Accordingly this module does **not** invent boundary conditions.  It provides
the honest substrate on which a thermodynamic limit can be stated:

* `CompatibleLocalObservable` gives one bounded measurable local observable
  by finite abstract coordinates and embeddings into every sufficiently
  large torus;
* `CompatibleLocalObservable.plaquetteHolonomy` supplies a nonempty,
  geometrically coherent four-edge instance;
* `localGibbsExpectation` is literally `expectation`, hence an integral
  against the genuine Gibbs measure;
* bounded measurable plaquette energy discharges Gibbs normalization through
  the already-banked `gibbsMeasure_isProbability'`;
* `pinnedBoundaryRemainder` is the explicit one-volume pinned-tail expression;
* `pinnedBoundaryRemainder_le_volumeUniform` is wholly finite-volume.  It applies
  `connectedLattice_pinned_tail_volumeUniform` to every pinned polymer and
  then uses
  `connectedLatticePolymerSystem_tilt_kpCriterion_volumeUniform` to sum all
  polymers touching the support anchor.

There is deliberately no convergence theorem here.  In particular, no free
`bulk : ℝ` is postulated: such a parameter would already encode the
infinite-volume object that a thermodynamic-limit theorem must construct.
The missing concrete brick is an exact finite-volume expansion of the genuine
local Gibbs expectation, followed by stabilization of the local cluster
contribution.  Until that is proved, this module is substrate, not a
thermodynamic-limit closure.

## Rejected measured failure

An earlier draft exposed
`localGibbsExpectation_tendsto_of_pinnedExpansion` and
`localGibbsExpectation_cauchySeq_of_pinnedExpansion` under the hypothesis

```
∀ n, |localGibbsExpectation μ pe β O n - bulk|
  = pinnedBoundaryRemainder ... n ...
```

with a free `bulk : ℝ`.  Those implications were true, but unsuitable as a
thermodynamic-limit interface: `bulk` is not finite-volume data, and the
hypothesis already postulates the common infinite-volume value whose
construction is the hard theorem.  The endpoints were therefore removed from
the verified interface, and this diagnosis is retained to prevent the same
failure mode from being reconstructed.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open Filter MeasureTheory KP
open scoped BigOperators Topology

section LocalObservable

variable (d : ℕ) [NeZero d] (G : Type*) [Group G] [MeasurableSpace G]

/-- A bounded measurable local observable with volume-independent coordinates.
`coord s` is the natural-number source coordinate and positive direction of
the edge labelled by `s`.  At side `n+1`, `edgeAt` reduces the source modulo
`n+1`; `coord_lt` makes this reduction injective once `n ≥ minVolume`.
Thus the same finite coordinate pattern, not an arbitrary new embedding, is
realized in every sufficiently large torus. -/
structure CompatibleLocalObservable where
  Support : Type*
  [supportFintype : Fintype Support]
  coord : Support → (Fin d → ℕ) × Fin d
  coord_injective : Function.Injective coord
  minVolume : ℕ
  coord_lt : ∀ s j, (coord s).1 j < minVolume + 1
  kernel : (Support → G) → ℝ
  kernel_measurable : Measurable kernel
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  kernel_bound : ∀ x, |kernel x| ≤ bound

attribute [instance] CompatibleLocalObservable.supportFintype

namespace CompatibleLocalObservable

variable {d G}

/-- Reduction of an abstract positive edge coordinate into the side-`n+1`
torus. -/
def edgeAt
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (_h : O.minVolume ≤ n) (s : O.Support) : PosEdge d (n + 1) :=
  ⟨⟨fun j =>
      ⟨(O.coord s).1 j % (n + 1), Nat.mod_lt _ (by omega)⟩,
    (O.coord s).2, true⟩, rfl⟩

omit [NeZero d] [Group G] in
/-- The modulo realization of the abstract support is injective at every
admissible volume. -/
theorem edgeAt_injective
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) :
    Function.Injective (O.edgeAt n h) := by
  intro s t hst
  apply O.coord_injective
  apply Prod.ext
  · funext j
    have hj := congrArg (fun e => (e.1.source j).val) hst
    simp only [edgeAt] at hj
    have hslt : (O.coord s).1 j < n + 1 :=
      lt_of_lt_of_le (O.coord_lt s j) (by omega)
    have htlt : (O.coord t).1 j < n + 1 :=
      lt_of_lt_of_le (O.coord_lt t j) (by omega)
    simpa [Nat.mod_eq_of_lt hslt, Nat.mod_eq_of_lt htlt] using hj
  · have hdir := congrArg (fun e => e.1.dir) hst
    simpa [edgeAt] using hdir

/-- Canonical embedding of the fixed abstract support into an admissible
finite torus. -/
def edgeEmbedding
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) : O.Support ↪ PosEdge d (n + 1) :=
  ⟨O.edgeAt n h, O.edgeAt_injective n h⟩

open Classical in
/-- The concrete positive-edge support of `O` in an admissible torus. -/
noncomputable def realizedSupport
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) : Finset (PosEdge d (n + 1)) :=
  Finset.univ.map (O.edgeEmbedding n h)

open Classical in
@[simp]
theorem edgeAt_mem_realizedSupport
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) (s : O.Support) :
    O.edgeAt n h s ∈ O.realizedSupport n h := by
  exact Finset.mem_map.mpr ⟨s, Finset.mem_univ s, rfl⟩

open Classical in
@[simp]
theorem card_realizedSupport
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) :
    (O.realizedSupport n h).card = Fintype.card O.Support := by
  unfold realizedSupport
  rw [Finset.card_map, Finset.card_univ]

/-- Restrict a torus gauge configuration to the abstract support of a local
observable. -/
noncomputable def restrictConfig
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) (A : GaugeConfig d (n + 1) G) :
    O.Support → G :=
  fun s => configToPos A (O.edgeEmbedding n h s)

/-- Realization of a compatible local observable on the side-`n+1` torus.
The finitely many undersized volumes are set to zero and therefore do not
affect any cofinal limit. -/
noncomputable def realize
    (O : CompatibleLocalObservable d G) (n : ℕ) :
    GaugeConfig d (n + 1) G → ℝ :=
  if h : O.minVolume ≤ n then fun A => O.kernel (O.restrictConfig n h A)
  else fun _ => 0

/-- The realization is measurable on every torus. -/
theorem measurable_realize
    (O : CompatibleLocalObservable d G) (n : ℕ) :
    Measurable (O.realize n) := by
  unfold realize
  split_ifs with h
  · apply O.kernel_measurable.comp
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (O.edgeEmbedding n h s)).comp
      (gaugeConfigMEquiv (d := d) (N := n + 1) (G := G)).symm.measurable
  · exact measurable_const

/-- The uniform sup bound survives realization. -/
theorem abs_realize_le
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    |O.realize n A| ≤ O.bound := by
  unfold realize
  split_ifs with h
  · exact O.kernel_bound _
  · simpa using O.bound_nonneg

open Classical in
/-- The complex cast of an admissible realization reads exactly the finite
positive-edge support supplied by `realizedSupport`.  This is the bridge from
the volume-independent observable interface to the product-Haar
factorization machinery. -/
theorem dependsOnPos_realize
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) :
    DependsOnPos (fun A : GaugeConfig d (n + 1) G => (O.realize n A : ℂ))
      (O.realizedSupport n hvol) := by
  intro x y hxy
  simp only [realize, dif_pos hvol]
  congr 1
  apply congrArg O.kernel
  funext s
  unfold restrictConfig
  have hx : configToPos (posToConfig x) = x :=
    (gaugeConfigEquiv (d := d) (N := n + 1) (G := G)).left_inv x
  have hy : configToPos (posToConfig y) = y :=
    (gaugeConfigEquiv (d := d) (N := n + 1) (G := G)).left_inv y
  rw [hx, hy]
  exact hxy _ (O.edgeAt_mem_realizedSupport n hvol s)

/-- A non-vacuity witness: every constant is a compatible local observable
with empty support. -/
noncomputable def const (c : ℝ) : CompatibleLocalObservable d G where
  Support := Fin 0
  coord := fun i => Fin.elim0 i
  coord_injective := fun i => Fin.elim0 i
  minVolume := 0
  coord_lt := fun i => Fin.elim0 i
  kernel := fun _ => c
  kernel_measurable := measurable_const
  bound := |c|
  bound_nonneg := abs_nonneg c
  kernel_bound := fun _ => le_rfl

@[simp]
theorem realize_const (c : ℝ) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    (const (d := d) (G := G) c).realize n A = c := by
  simp [realize, const]

private def plaquetteDir0 (hd : 2 ≤ d) : Fin d :=
  ⟨0, by omega⟩

private def plaquetteDir1 (hd : 2 ≤ d) : Fin d :=
  ⟨1, by omega⟩

/-- The volume-independent source coordinate and positive direction of each
edge in the oriented plaquette at the origin. -/
private def plaquetteCoord
    (hd : 2 ≤ d) : Fin 4 → (Fin d → ℕ) × Fin d
  | ⟨0, _⟩ => ⟨fun _ => 0, plaquetteDir0 hd⟩
  | ⟨1, _⟩ =>
      ⟨fun j => if j = plaquetteDir0 hd then 1 else 0,
        plaquetteDir1 hd⟩
  | ⟨2, _⟩ =>
      ⟨fun j => if j = plaquetteDir1 hd then 1 else 0,
        plaquetteDir0 hd⟩
  | ⟨3, _⟩ => ⟨fun _ => 0, plaquetteDir1 hd⟩

private lemma plaquetteCoord_injective
    (hd : 2 ≤ d) :
    Function.Injective (plaquetteCoord (d := d) hd) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [plaquetteCoord] at hij ⊢
  all_goals
    exfalso
    have hcode := congrArg (fun c =>
      (c.2.val, c.1 (plaquetteDir0 hd), c.1 (plaquetteDir1 hd))) hij
    norm_num [plaquetteDir0, plaquetteDir1] at hcode

/-- A genuine nonempty compatible local observable: apply a bounded measurable
real function to the oriented holonomy of the fixed plaquette at the origin.
Its support is `Fin 4`; hence this construction exercises the volume-indexed
edge embeddings rather than using the empty support of `const`.

For `SU(N)`, taking `f` to be the real trace gives the standard local
plaquette-trace observable. -/
noncomputable def plaquetteHolonomy
    [MeasurableMul₂ G] [MeasurableInv G]
    (hd : 2 ≤ d) (f : G → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ g, |f g| ≤ C) :
    CompatibleLocalObservable d G where
  Support := Fin 4
  coord := plaquetteCoord hd
  coord_injective := plaquetteCoord_injective hd
  minVolume := 1
  coord_lt := by
    intro s j
    have hdir : plaquetteDir0 hd ≠ plaquetteDir1 hd := by
      intro h
      exact Nat.zero_ne_one (congrArg Fin.val h)
    fin_cases s <;>
      by_cases hj0 : j = plaquetteDir0 hd <;>
      by_cases hj1 : j = plaquetteDir1 hd <;>
      simp [plaquetteCoord, hj0, hj1, hdir, hdir.symm]
  kernel := fun x => f (x 0 * x 1 * (x 2)⁻¹ * (x 3)⁻¹)
  kernel_measurable := by fun_prop
  bound := C
  bound_nonneg := hC
  kernel_bound := fun x => hfC _

end CompatibleLocalObservable

end LocalObservable

section GenuineGibbsExpectation

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableMul₂ G] [MeasurableInv G]

/-- The finite-volume value of a compatible local observable.  This is the
actual Gibbs integral, not a quotient or a cluster-expansion surrogate. -/
noncomputable def localGibbsExpectation
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) : ℝ :=
  expectation d (n + 1) μ pe β (O.realize n)

/-- Bounded local observables are integrable against the genuine finite-volume
Gibbs probability measure; `h_int` is discharged by the banked bounded-energy
theorem. -/
theorem integrable_realize_gibbs
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) :
    Integrable (O.realize n)
      (gibbsMeasure (d := d) (N := n + 1) μ pe β) := by
  letI : IsProbabilityMeasure
      (gibbsMeasure (d := d) (N := n + 1) μ pe β) :=
    gibbsMeasure_isProbability' μ hpe_meas hpe β
  refine (integrable_const O.bound).mono'
    (O.measurable_realize n).aestronglyMeasurable ?_
  exact ae_of_all _ fun A => by
    simpa [Real.norm_eq_abs] using O.abs_realize_le n A

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Positivity of a genuine finite-volume Gibbs expectation. -/
theorem localGibbsExpectation_nonneg
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hO : ∀ A, 0 ≤ O.realize n A) :
    0 ≤ localGibbsExpectation μ pe β O n := by
  unfold localGibbsExpectation expectation
  exact integral_nonneg hO

/-- The genuine finite-volume Gibbs expectation of `1` is exactly `1`, with
bounded-energy integrability discharged rather than assumed. -/
theorem localGibbsExpectation_one
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (n : ℕ) :
    localGibbsExpectation μ pe β
      (CompatibleLocalObservable.const (d := d) (G := G) 1) n = 1 := by
  unfold localGibbsExpectation
  simpa using expectation_const d (n + 1) μ pe β
    (integrable_boltzmann μ hpe_meas hpe β) 1

end GenuineGibbsExpectation

section PinnedRemainder

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

open Classical in
/-- The explicit one-volume sum of pinned tails over every polymer
incompatible with (hence touching) the local support anchor. -/
noncomputable def pinnedBoundaryRemainder
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (anchor : (connectedLatticePolymerSystem (d := d) (N := N)
      μ pe β).Polymer)
    (L K : ℕ) : ℝ :=
  ∑ c ∈ (Finset.univ :
      Finset (connectedLatticePolymerSystem (d := d) (N := N)
        μ pe β).Polymer).filter
      (fun c => (connectedLatticePolymerSystem (d := d) (N := N)
        μ pe β).incomp anchor c),
    ∑ n ∈ Finset.range (K + 1),
      pinnedClusterWeightGE
        (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
        (fun c => c.1.card) c L n

/-- **Finite-volume pinned-tail estimate.**

The proof applies the banked pinned-tail theorem pointwise and then uses the
tilted volume-uniform KP criterion to sum *all* polymers incompatible with the
chosen anchor.  Thus the prefactor is `t * |anchor|`, with no volume
cardinality.  No infinite-volume reference value occurs in the statement. -/
theorem pinnedBoundaryRemainder_le_volumeUniform
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (anchor : (connectedLatticePolymerSystem (d := d) (N := N)
      μ pe β).Polymer)
    (L K : ℕ) :
    pinnedBoundaryRemainder μ pe β anchor L K ≤ Real.exp (-(ε * L)) *
      (t * (anchor.1.card : ℝ)) := by
  classical
  have htail : ∀ c :
      (connectedLatticePolymerSystem (d := d) (N := N) μ pe β).Polymer,
      (∑ n ∈ Finset.range (K + 1),
        pinnedClusterWeightGE
          (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
          (fun c => c.1.card) c L n) ≤
        Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) *
            ‖(connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) :=
    fun c => connectedLattice_pinned_tail_volumeUniform
      μ hpe β t ε ht0 hε0 hr hsmall c L K
  have hcrit :=
    connectedLatticePolymerSystem_tilt_kpCriterion_volumeUniform
      (d := d) (N := N) μ hpe β t ε ht0 hr hsmall
  have hsum := hcrit.2 anchor
  unfold pinnedBoundaryRemainder
  calc
    (∑ c ∈ (Finset.univ :
        Finset (connectedLatticePolymerSystem (d := d) (N := N)
          μ pe β).Polymer).filter
        (fun c => (connectedLatticePolymerSystem (d := d) (N := N)
          μ pe β).incomp anchor c),
      ∑ n ∈ Finset.range (K + 1),
        pinnedClusterWeightGE
          (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
          (fun c => c.1.card) c L n)
      ≤ ∑ c ∈ (Finset.univ :
          Finset (connectedLatticePolymerSystem (d := d) (N := N)
            μ pe β).Polymer).filter
          (fun c => (connectedLatticePolymerSystem (d := d) (N := N)
            μ pe β).incomp anchor c),
        Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) *
            ‖(connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) :=
      Finset.sum_le_sum fun c _ => htail c
    _ = Real.exp (-(ε * L)) *
        ∑ c ∈ (Finset.univ :
          Finset (connectedLatticePolymerSystem (d := d) (N := N)
            μ pe β).Polymer).filter
          (fun c => (connectedLatticePolymerSystem (d := d) (N := N)
            μ pe β).incomp anchor c),
          Real.exp (ε * (c.1.card : ℝ)) *
            ‖(connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).activity c‖ *
            Real.exp (t * (c.1.card : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-(ε * L)) * (t * (anchor.1.card : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      simpa [KP.tilt_norm_activity, mul_assoc, mul_left_comm, mul_comm] using hsum

end PinnedRemainder

end YangMills
