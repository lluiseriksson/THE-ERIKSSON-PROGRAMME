# PETER-WEYL ROADMAP

**Target:** prove `ConnectedCorrDecay (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F distP`
for genuine Wilson observables `F` and the actual SU(N_c) Gibbs measure, at small β.

**Status:** strategic design only. No Lean code in this document. No commits.

**Date:** 2026-04-19. Author role: strategist.

---

## 0. Executive summary

The live bottleneck is the `bound` field of the `ConnectedCorrDecay` structure
(`YangMills/P3_BalabanRG/CorrelationNorms.lean`):

```
|wilsonConnectedCorr μ plaquetteEnergy β F p q|
    ≤ C * Real.exp (-m * distP N p q)
```

for `μ := sunHaarProb N_c`, `plaquetteEnergy := wilsonPlaquetteEnergy N_c`.

Every downstream target (`ClayYangMillsPhysicalStrong`, `ClayYangMillsStrong`,
`ClayYangMillsTheorem`) reduces to this single bound once `F`, `β`, and `distP`
are fixed to genuine Wilson choices. The project has the algebraic bridge
from `r^dist` to `exp(-m·dist)` (`rpow_le_exp_kpParameter`) and the
Fubini / sum-integral interchange for the partition function
(`integral_boltzmann_eq_sum_activities`). What it does **not** have is the
pointwise correlator bound itself, and that bound is exactly what the
Osterwalder–Seiler / Kotecky–Preiss chain produces — but only after four
Mathlib contributions that do not yet exist are in place.

This document lays out those contributions as a six-layer dependency graph,
assigns line-count estimates and risk to each, orders the critical path,
and identifies the first milestone that is provable in one Colab session
with existing Mathlib. The first milestone is `sunHaarProb_trace_re_integral_zero`:
the real part of the trace of an SU(N_c) matrix integrates to zero against
the Haar probability measure for `N_c ≥ 2`. This is the first non-trivial
Schur-orthogonality fact on the critical path, and its proof uses only
Haar left-invariance plus the existence of a non-trivial central element.

---

## 1. Target statement

From `YangMills/P3_BalabanRG/CorrelationNorms.lean`:

```
structure ConnectedCorrDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) where
  C  : ℝ
  m  : ℝ
  hC : 0 ≤ C
  hm : 0 < m
  bound :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q|
        ≤ C * Real.exp (-m * distP N p q)
```

Concrete instantiation to close:

* `G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)`
* `μ := sunHaarProb N_c := Measure.haarMeasure (sunPositiveCompacts N_c)`
* `plaquetteEnergy := wilsonPlaquetteEnergy N_c := fun U => (U.val.trace).re`
* `β` small, positive
* `F` a genuine Wilson class observable (e.g. a finite linear combination
  of characters)
* `distP` = `fun N p q => siteLatticeDist p.site q.site`

`wilsonConnectedCorr` is the connected two-plaquette correlator under the
Gibbs tilt: the Wilson-Gibbs measure is `(Measure.pi μ).tilted (-β · wilsonAction)`
after pullback along `gaugeConfigEquiv` (see `L1_GibbsMeasure/GibbsMeasure.lean`).

The correlator pairs the value of `F` at two plaquettes `p`, `q` in the
lattice; "connected" means `⟨F_p · F_q⟩ − ⟨F_p⟩·⟨F_q⟩`.

---

## 2. Mathlib availability map (honest)

### AVAILABLE in Mathlib (current rev)

* `MeasureTheory.Measure.haarMeasure` — Haar probability measure on a
  compact topological group, used directly in `sunHaarProb`.
* `MeasureTheory.Measure.IsHaarMeasure` and left-invariance API
  (`MeasureTheory.Measure.integral_eq_integral_smul` and
  `MeasureTheory.lintegral_haarMeasure_eq_lintegral_haarMeasure` variants,
  `MeasureTheory.Measure.map_mul_left_eq_self`).
* `Matrix.specialUnitaryGroup`, its topological group instance,
  `IsCompact (Set.univ : Set (specialUnitaryGroup ...))` is derivable from
  the closed subset of the unitary group; `CompactSpace` instance already
  instantiated in `P8_PhysicalGap/SUN_StateConstruction.lean`.
* `MeasureTheory.L2`, `Lp`, inner-product structure on `L²(G; ℂ)` for
  `G` a compact group with Haar.
* `ContinuousFunction.Algebra`, Stone–Weierstrass on compact Hausdorff
  (`ContinuousMap.StoneWeierstrass`).
* Character theory for **finite** groups: `Representation`, `FdRep`,
  `Representation.character`, orthogonality over finite groups.
* `Module.End.Schur` — Schur's lemma as a module-endomorphism fact over
  a field for simple modules.
* Classical analysis: `Real.exp_sum`, `Finset.prod_exp`, `Real.rpow_def_of_pos`,
  `Real.log_nonpos`, `MeasureTheory.integral_finset_sum`.
* `MeasureTheory.Measure.pi` and `MeasureTheory.Measure.tilted`.
* `Complex.abs_exp`, modulus and phase for `Complex`.

### PARTIAL in Mathlib

* `Representation R G V` — continuous representations exist as a concept,
  but matrix coefficients as functions `G → ℂ` and their `L²` structure are
  not packaged together for compact Lie groups.
* Unitary representation theory for compact groups — some scaffolding in
  `Mathlib.RepresentationTheory`, but the full decomposition theorem is
  not present.
* Haar uniqueness up to scaling on compact Hausdorff groups (`Mathlib.
  MeasureTheory.Group.Measure`) — yes, but not specialised to compact Lie
  groups with explicit normalisation constants.
* `Mathlib.Analysis.Fourier.AddCircle` provides the abelian prototype of
  Peter–Weyl (Fourier series on the circle). The generalisation to
  non-abelian compact groups is not present.
* Modified Bessel functions `I_n(z)` — `Mathlib.Analysis.SpecialFunctions`
  has some special-function machinery but not the SU(2) character-expansion
  coefficients explicitly.

### MISSING in Mathlib

1. **Peter–Weyl decomposition theorem** for compact Lie groups:
   `L²(G) ≃ ⨁_{ρ ∈ Ĝ} V_ρ ⊗ V_ρ*` as unitary G-representations, where
   the sum ranges over isomorphism classes of irreducible unitary
   finite-dimensional representations.
2. **Schur orthogonality for matrix coefficients** against Haar:
   `∫ ρ_ij(g) · conj (σ_kl(g)) dHaar = δ_{ρ,σ} δ_{i,k} δ_{j,l} / dim(ρ)`.
3. **Character expansion of Wilson-like class functions**:
   for `f : G → ℂ` a continuous class function, the series
   `f(g) = ∑_ρ a_ρ χ_ρ(g)` converges in `L²` with
   `a_ρ = ∫ f(g) conj χ_ρ(g) dHaar / dim(ρ)`. For the specific class
   function `exp(-β · Re tr U)` on SU(N_c), the Osterwalder–Seiler
   estimate `|a_ρ(β)| ≤ C_ρ · β^{|ρ|}` (with `|ρ|` the number of boxes
   in the Young diagram of `ρ`).
4. **SU(N_c) irrep catalogue beyond the fundamental**: Young-diagram /
   weight-space enumeration; dimension formula; explicit structure of
   the tensor products that show up when you expand products of traces.
5. **Kotecky–Preiss / Mayer cluster expansion convergence theorem** for
   polymer models with `|K(γ)| ≤ r^{|γ|}` and small `r`, yielding
   exponential decay of connected correlators.

This is roughly one major Mathlib PR per missing item, plus a final
project-local PR to glue them.

---

## 3. Six-layer roadmap

The arrows indicate strict dependency: each later layer consumes definitions
and theorems from earlier layers.

```
Layer 0  Mathlib extensions (irreducible reps, matrix coefficients, Haar L²)
   ↓
Layer 1  Peter–Weyl for compact Lie groups
   ↓
Layer 2  Schur orthogonality for matrix coefficients and characters
   ↓
Layer 3  Character expansion of exp(-β · Re tr U) with β-power coefficient bounds
   ↓
Layer 4  Kotecky–Preiss polymer cluster expansion, small-β convergence
   ↓
Layer 5  Assembly: close ConnectedCorrDecay, chain to ClayYangMillsPhysicalStrong
```

### Layer 0 — Mathlib extensions (foundation)

Sub-items:

* **L0.1** `ContinuousRep G V := Representation ℂ G V` bundled with
  `ContinuousSMul G V` and finite-dimensionality. Currently scattered;
  consolidate into a structure suitable for compact-group work.
* **L0.2** Matrix coefficient API: for `ρ : ContinuousRep G V` with
  a chosen orthonormal basis, the functions
  `matCoeff ρ i j : G → ℂ, g ↦ ⟨e_i, ρ g · e_j⟩` live in `C(G, ℂ)` and
  in `L²(G, Haar)`.
* **L0.3** `CharacterFunction ρ : G → ℂ, g ↦ trace (ρ g)` with continuity
  and centrality (`χ_ρ(h g h⁻¹) = χ_ρ(g)`).
* **L0.4** `L²(G, Haar, ℂ)` as a Hilbert space with explicit
  Stone–Weierstrass density of `⟨matrix coefficients⟩ ⊆ C(G,ℂ) ⊆ L²(G,ℂ)`.

**Estimated LOC:** ~500–1200. **Mathlib-PR-friendly:** yes. **Risk:**
moderate; depends on state of `Mathlib.RepresentationTheory.FdRep` refactors.

**Lean statement sketch (not code):**

```
structure ContinuousFiniteRep (G : Type*) [Group G] [TopologicalSpace G]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] extends Representation ℂ G V where
  continuous : Continuous (fun g : G => (toRepresentation g : V →L[ℂ] V))
  unitary    : ∀ g, IsometryEquiv (toRepresentation g)
```

### Layer 1 — Peter–Weyl for compact Lie groups

Sub-items:

* **L1.1** For `G` a compact Hausdorff topological group and `Ĝ` the set of
  isomorphism classes of irreducible continuous unitary finite-dimensional
  representations, the matrix-coefficient family
  `{ √(dim ρ) · matCoeff ρ i j | ρ ∈ Ĝ, 1 ≤ i,j ≤ dim ρ }` is an
  **orthonormal** family in `L²(G, Haar)`.
* **L1.2** The same family is **total** (its span is dense): closure of
  the linear span under `L²` norm equals the whole space. Via
  Stone–Weierstrass on `C(G, ℂ)` once it is shown that matrix coefficients
  separate points and contain constants — this requires the existence of
  enough irreducible representations, which follows from the
  Gelfand–Raikov theorem on compact groups.
* **L1.3** Package as a unitary isomorphism
  `L²(G) ≃ ⨁_{ρ ∈ Ĝ} (V_ρ ⊗ V_ρ*)` of `G × G`-representations.
* **L1.4** Specialisation to class functions: characters `{χ_ρ}` form a
  Hilbert basis of the subspace `L²(G)^{conj}` of class functions.

**Estimated LOC:** ~2500–5000. **Mathlib-PR-friendly:** yes, but a large
PR. **Risk:** HIGH. Peter–Weyl is the single biggest external
mathematical contribution and has never been formalised in Lean to my
knowledge. In Isabelle/HOL there is a version (Hölzl, Immler); in Coq
there is partial work. Importing the proof strategy from those libraries
is feasible but time-intensive.

**Lean statement sketch:**

```
theorem peter_weyl_orthonormal {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [IsTopologicalGroup G] [T2Space G]
    (ρ σ : IrrContinuousRep G) (i j : Fin ρ.dim) (k l : Fin σ.dim) :
    ∫ g, matCoeff ρ i j g * conj (matCoeff σ k l g) ∂(haarProb G) =
      if ρ = σ ∧ i = k ∧ j = l then (1 : ℂ) / ρ.dim else 0

theorem peter_weyl_total {G : Type*} [...] :
    DenseRange (fun (⟨ρ, i, j⟩ : …) => matCoeff ρ i j : … → C(G, ℂ))
```

### Layer 2 — Schur orthogonality for matrix coefficients and characters

Sub-items:

* **L2.1** `∫ χ_ρ · conj χ_σ dHaar = [ρ = σ]`: characters form an
  orthonormal system (immediate corollary of L1.1 plus trace identity).
* **L2.2** Character expansion for class functions:
  `f = ∑_ρ ⟨f, χ_ρ⟩_{L²} · χ_ρ` with `ℓ²` summable coefficients.
* **L2.3** **Integrated-moment calculation on SU(N_c):** the fact that
  `∫ (tr U) dHaar = 0` for `N_c ≥ 2`, and more generally the Weingarten /
  moment formulas for polynomials in matrix entries. The degree-1
  vanishing is the **first milestone** (see §4).

**Estimated LOC:** ~400–900. **Mathlib-PR-friendly:** yes, once Layer 1
is in place. **Risk:** LOW given Layer 1; standalone first-milestone
subset is LOW even without Layer 1.

**Lean statement sketch (first milestone in bold):**

```
/-- First milestone. Provable in isolation using only Haar left-invariance
    and the non-trivial centre element ω · I with ω = exp(2πi/N_c). -/
theorem sunHaarProb_trace_re_integral_zero
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U, (U.val.trace).re ∂(sunHaarProb N_c) = 0
```

### Layer 3 — Character expansion of `exp(-β · Re tr U)`

Sub-items:

* **L3.1** The Wilson plaquette weight `U ↦ exp(-β · Re tr U)` is a
  continuous class function on SU(N_c) (centrality is trivial because
  `Re tr` is a class function and `exp ∘ (linear)` preserves centrality).
* **L3.2** Expand: `exp(-β · Re tr U) = ∑_ρ a_ρ(β) · χ_ρ(U)` in `L²`,
  with `a_ρ(β) = ∫ exp(-β Re tr U) · conj χ_ρ(U) dHaar`.
* **L3.3** **Small-β coefficient bound (Osterwalder–Seiler):**
  `|a_ρ(β)| ≤ (C_N β)^{|ρ|} / |ρ|!`, where `|ρ|` is the number of boxes
  in the Young diagram of `ρ`. Proof by Taylor expansion of `exp` and
  Schur orthogonality term-by-term, using the fact that `(Re tr U)^k`
  is a polynomial in the fundamental and anti-fundamental characters of
  degree `k`.
* **L3.4** Uniform-convergence upgrade on SU(N_c): because characters
  are uniformly bounded (`|χ_ρ(U)| ≤ dim ρ`) and `|a_ρ(β)|` decays
  faster than any polynomial in `dim ρ` for small `β`, the series
  converges absolutely and uniformly on SU(N_c).

**Estimated LOC:** ~800–1800. **Mathlib-PR-friendly:** probably
project-local (the SU(N_c) specialisation is too specific for Mathlib).
**Risk:** HIGH. The combinatorial identification of Young-diagram
degree with the number of fundamental-character factors in `(Re tr U)^k`
is the single most technical step of this layer. For `N_c = 2` the
answer is classical (modified Bessel function `I_{n+1}(β)/I_1(β)`); for
`N_c ≥ 3` one needs the full Young-diagram machinery or a uniform bound
via a contour-integral representation (Gross–Taylor).

**Lean statement sketch:**

```
theorem wilson_character_coefficient_bound
    (N_c : ℕ) [NeZero N_c] (β : ℝ) (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (ρ : IrrContinuousRep (specialUnitaryGroup (Fin N_c) ℂ)) :
    |∫ U, Real.exp (-β * (U.val.trace).re) *
          ((characterFunction ρ U).re) ∂(sunHaarProb N_c)| ≤
    (N_c : ℝ) ^ ρ.youngSize * β ^ ρ.youngSize / (ρ.youngSize).factorial
```

### Layer 4 — Kotecky–Preiss cluster expansion

Sub-items:

* **L4.1** Polymer model definition: a polymer `γ` on the lattice is a
  connected set of plaquettes; the polymer activity is
  `K(γ) = ∫ ∏_{p ∈ γ} (plaquetteWeight_p - 1) dHaar_{edges of γ}`
  (this is `wilsonClusterActivityRaw` in the existing codebase).
* **L4.2** **Amplitude bound via L3**: plug the character expansion of
  `exp(-β · Re tr U) - 1` into the activity integral; the leading term
  is `∑_{ρ ≠ trivial} a_ρ(β) χ_ρ(U)`. Using Schur orthogonality on
  *shared edges* between adjacent plaquettes within a polymer, the
  integral factorises over a spanning-tree structure, giving
  `|K(γ)| ≤ (C_N β)^{|γ|}` where `|γ|` is the plaquette count of the
  polymer.
* **L4.3** Kotecky–Preiss criterion: for `r := C_N β` small enough,
  `∑_{γ ∋ p} |K(γ)| · e^{a|γ|} ≤ a` for some `a > 0`. Standard
  combinatorial lemma.
* **L4.4** Cluster-expansion convergence theorem: the log of the
  partition function has a convergent polymer expansion, and the
  connected correlator obeys
  `|⟨F_p ; F_q⟩| ≤ C · r^{dist(p,q)}` (polymer-size bound;
  `rpow_le_exp_kpParameter` converts this to exponential form).

**Estimated LOC:** ~1500–3500. **Mathlib-PR-friendly:** the Kotecky–Preiss
criterion itself is a clean combinatorial theorem and may be Mathlib-bound;
the specialisation to the Wilson gauge model is project-local. **Risk:**
MODERATE. Kotecky–Preiss is well-established mathematically (1986,
MRS / Balaban / Brydges re-expositions). The Lean formalisation has
not been done before but is book-level.

**Lean statement sketch:**

```
theorem wilson_polymer_activity_bound
    (N_c : ℕ) [NeZero N_c] {β : ℝ} (hβ : 0 < β)
    (hβ_small : β < βCrit N_c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ {d L} [NeZero d] [NeZero L] (γ : Polymer d L),
        |wilsonClusterActivityRaw N_c β γ.toFinset| ≤ r ^ γ.size

theorem kp_cluster_decay
    (N_c : ℕ) [NeZero N_c] {β : ℝ} (hβ : 0 < β)
    (hβ_small : β < βCrit N_c) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ {d L} [NeZero d] [NeZero L]
        (F : ↥(specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
        (_hF : ∀ U, |F U| ≤ 1)
        (p q : ConcretePlaquette d L),
        1 ≤ siteLatticeDist p.site q.site →
        |wilsonConnectedCorr (sunHaarProb N_c)
            (wilsonPlaquetteEnergy N_c) β F p q|
          ≤ C * r ^ siteLatticeDist p.site q.site
```

### Layer 5 — Assembly

Sub-items:

* **L5.1** Combine L4.4 with `rpow_le_exp_kpParameter` (already in
  `WilsonClusterProof.lean`) to convert the `r^dist` bound into
  `exp(-m · dist)` with `m = -log r / 2 > 0`.
* **L5.2** Package as `ConnectedCorrDecay` instance for
  `sunHaarProb N_c` / `wilsonPlaquetteEnergy N_c` / small `β` / any
  bounded class observable `F` / `distP := siteLatticeDist`.
* **L5.3** Chain through `connectedCorrDecay_implies_physicalStrong`
  (`L8_Terminal/ClayPhysical.lean`) to obtain
  `ClayYangMillsPhysicalStrong`, and downstream to
  `ClayYangMillsStrong` and `ClayYangMillsTheorem`.

**Estimated LOC:** ~400–700. **Mathlib-PR-friendly:** no (project-local
assembly). **Risk:** LOW. This layer is essentially the glue already
designed in `ClusterCorrelatorBound.lean` and `WilsonClusterProof.lean`;
once L1–L4 are in, assembly is mechanical.

---

## 4. First achievable milestone

**Target:**

```
theorem sunHaarProb_trace_re_integral_zero
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) :
    ∫ U, (U.val.trace).re ∂(sunHaarProb N_c) = 0
```

**Why this one:**

1. **On the critical path.** It is the first non-trivial Schur-orthogonality
   statement on SU(N_c) and a degree-1 instance of the Osterwalder–Seiler
   coefficient bound (the coefficient `a_{triv}(0)` computed differently).
2. **Provable with existing Mathlib.** Uses only:
   * `MeasureTheory.Measure.IsHaarMeasure.isMulLeftInvariant` — Haar is
     left-invariant under multiplication by any group element.
   * `MeasureTheory.integral_map_equiv` (or the translation-of-integral
     lemma for left-invariant measures) — a left-translation of the
     integrand leaves the integral unchanged.
   * Linearity of the Bochner integral over `ℝ` (the trace is a linear
     functional of `U` and `(·).re` is ℝ-linear).
   * Simple algebraic identity on scalar matrices: for `ω ∈ ℂ` with
     `ω^{N_c} = 1` and `ω ≠ 1`, the matrix `ω · I` is in SU(N_c) iff
     `ω^{N_c} = 1` and additionally `det (ω · I) = ω^{N_c} = 1` (yes),
     and `tr (ω · I · U) = ω · tr U`.
3. **Session-sized.** ~100–200 Lean lines. One Colab build.
4. **Standalone.** Does not require Peter–Weyl; does not require the
   character-expansion machinery; does not interact with Gibbs
   measures. A clean, self-contained proof.

**Proof sketch (mathematical, not Lean):**

Let `ω := exp(2πi / N_c)` and `Ω := ω · (1 : Matrix (Fin N_c) (Fin N_c) ℂ)`.
Then `Ω ∈ SU(N_c)`: its determinant is `ω^{N_c} = 1`, and it is unitary
because `Ω * Ω† = ω · conj(ω) · I = I`. For `N_c ≥ 2`, `ω ≠ 1`.

By left-invariance of `sunHaarProb N_c`,

```
∫ U, (U.val.trace).re ∂(sunHaarProb N_c)
    = ∫ U, ((Ω · U).trace).re ∂(sunHaarProb N_c)
    = ∫ U, (ω · U.val.trace).re ∂(sunHaarProb N_c)
    = Re(ω) · ∫ U, (U.val.trace).re ∂(sunHaarProb N_c)
      − Im(ω) · ∫ U, (U.val.trace).im ∂(sunHaarProb N_c)
```

Repeating with `Ω' := ω² · I` and combining the two identities,
one gets `(ω - 1)` and `(ω² - 1)` times the two integrals equal zero,
forcing both real-part and imaginary-part integrals to vanish (the 2×2
coefficient matrix has determinant `(ω-1)(ω²-1)(ω+1)(ω+1) · ...` nonzero
for `N_c ≥ 3`; for `N_c = 2`, `ω = −1` and `Re(ω) = −1` immediately
gives `−2 · (∫ (tr).re) = 0`).

A cleaner argument: use the full centre `Z(SU(N_c)) = {ω^k · I | 0 ≤ k < N_c}`
and note that the map `U ↦ ω · U` on SU(N_c) preserves Haar, so the
integrand `U ↦ tr U` satisfies `∫ tr U = ω · ∫ tr U`, which for `ω ≠ 1`
forces `∫ tr U = 0` as a complex integral — then take real part.

**Fallback if that fails:** prove only the `N_c = 2` case first
(`sunHaarProb_trace_re_integral_zero_SU2`) using `Ω = -I ∈ SU(2)` and
linearity. This is ~50 lines.

**Non-goals for this milestone:**

* No character-expansion infrastructure.
* No general Schur orthogonality.
* No cluster expansion.
* No claim about `ClayYangMillsPhysicalStrong` or any downstream target.

---

## 5. Critical path and risk assessment

| Layer | LOC (low–high) | Risk  | Mathlib-suitable | Blocking |
|-------|---------------|-------|------------------|----------|
| L0    |   500–1200    | LOW   | yes              | L1       |
| L1    |  2500–5000    | HIGH  | yes (large PR)   | L2, L3   |
| L2    |   400–900     | LOW   | yes              | L3       |
| L3    |   800–1800    | HIGH  | project-local    | L4       |
| L4    |  1500–3500    | MOD   | partly Mathlib   | L5       |
| L5    |   400–700     | LOW   | project-local    | —        |
| **Σ** | **6100–13100**|       |                  |          |

**Dominant risk:** Layer 1 (Peter–Weyl). This is the single contribution
that (a) has never been done in Lean 4, (b) requires a careful interface
to Mathlib's `Representation` / `FdRep` / `ContinuousRep` machinery that
is itself under active refactor, and (c) has Lie-algebra dependencies
(continuity of the exponential map, analytic structure of compact Lie
groups) whose Mathlib status changes release-to-release.

**Alternative paths that reduce Layer-1 risk:**

* **Path A — Abelian warmup first:** close a U(1) version of the entire
  chain (L0–L5 specialised to abelian compact groups, where Peter–Weyl
  reduces to Fourier series on the circle, already in Mathlib as
  `Mathlib.Analysis.Fourier.AddCircle`). This gives
  `ClayYangMillsTheorem` for U(1) lattice gauge theory
  unconditionally and is estimated at 2000–4000 LOC total. It exercises
  every later layer but bypasses the Peter–Weyl bottleneck. The file
  `YangMills/ClayCore/AbelianU1Witness.lean` already exists as a
  starting point.
* **Path B — SU(2) special case only:** exploit the explicit
  parameterisation of SU(2) as `S^3`, the known character formula
  `χ_n(θ) = sin((n+1)θ) / sin(θ)`, and the modified-Bessel character
  expansion of `exp(-β cos θ)`. Skips generic Peter–Weyl entirely.
  Estimated 3000–6000 LOC. Closes `ClayYangMillsTheorem` for SU(2) only.
* **Path C — assume Peter–Weyl as an axiom for one or two release cycles**
  while pushing L2–L5 forward, then retire the axiom when Layer 1 lands.
  This violates the project's zero-axioms rule, so only viable if the
  project adopts a temporary "Mathlib-pending" axiom category. **Not
  recommended.**

**Recommended ordering for next 5 Colab sessions:**

1. **Session N+1:** prove the first milestone
   (`sunHaarProb_trace_re_integral_zero`). Standalone. Zero dependencies
   beyond current Mathlib.
2. **Session N+2:** extend to `sunHaarProb_trace_power_integral_bound`
   (coefficient bound for `(Re tr U)^k` against `exp(-β·...)`), for
   `k = 1, 2, 3` explicitly. This gives the first three Osterwalder–Seiler
   coefficients rigorously without needing Peter–Weyl.
3. **Session N+3:** close Layer 0 (matrix-coefficient API, continuity,
   L² inclusion) targeting Mathlib PR.
4. **Session N+4:** commit to Path A (U(1)) or Path B (SU(2)) for the
   end-to-end close. Decide based on how Layer 0 went.
5. **Session N+5:** execute the chosen path. Deliver a genuine,
   non-vacuous closure of `ClayYangMillsPhysicalStrong` for an abelian
   or SU(2) Wilson gauge model.

---

## 6. What this roadmap does not promise

* No claim that the full SU(N_c) roadmap is executable in a single Colab
  session, a single month, or a single reasonable project horizon.
* Layer 1 alone is of the size of a Mathlib merge event (Peter–Weyl
  has been a Mathlib wish-list item for years).
* Even with L1–L5 complete, `ClayYangMillsPhysicalStrong` admits
  trivial instantiations via degenerate observables or Dirac-supported
  measures; the project must separately demonstrate that the closed
  instance uses a non-degenerate `F` (e.g. a Wilson loop of non-trivial
  representation class) and the actual Wilson-Gibbs measure, not a
  pathological alternative. That non-degeneracy check is not itself on
  this roadmap — it is downstream of Layer 5.
* The full **continuum** Clay problem (no lattice, no cutoff) is
  strictly beyond every target in this document; `HasContinuumMassGap`
  is a statement about the lattice-to-continuum limit of
  `renormalizedMass`, which requires `a → 0` renormalisation-group
  control beyond the scope of this roadmap.

---

## 7. References

* Osterwalder–Seiler, *Gauge field theories on a lattice*,
  Ann. Physics **110** (1978) — character expansion and small-β bounds.
* Kotecky–Preiss, *Cluster expansion for abstract polymer models*,
  Commun. Math. Phys. **103** (1986).
* Balaban, *Large field renormalization. II. Localization, exponentiation,
  and bounds for the R operation*, Commun. Math. Phys. **122** (1989).
* Brydges, *A short course on cluster expansions*, Les Houches (1986).
* Hölzl & Immler, *Peter–Weyl theorem in Isabelle/HOL* — reference for
  a comparable formalisation in a different proof assistant.
* Mathlib: `MeasureTheory.Measure.Haar.Basic`,
  `Mathlib.Analysis.Fourier.AddCircle`,
  `Mathlib.RepresentationTheory.FdRep`,
  `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`.

---

**End of PETER_WEYL_ROADMAP.md**
