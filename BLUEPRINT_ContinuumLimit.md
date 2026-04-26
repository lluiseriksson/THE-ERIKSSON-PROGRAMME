# BLUEPRINT_ContinuumLimit.md

**Author**: Cowork agent (Claude), strategic blueprint 2026-04-25
**Subject**: genuine continuum-limit framework for Yang-Mills,
addressing Finding 004 + executing Option C of
`GENUINE_CONTINUUM_DESIGN.md`
**Branch**: VII of `OPENING_TREE.md`
**Companion**: `BLUEPRINT_F3Count.md`, `BLUEPRINT_F3Mayer.md`,
`BLUEPRINT_BalabanRG.md` (forthcoming)

---

## 0. Why this blueprint exists

`COWORK_FINDINGS.md` Finding 004 surfaced that the project's
`HasContinuumMassGap m_lat` predicate is satisfied via a
**coordinated scaling artifact**: with `latticeSpacing N = 1/(N+1)`
and the chosen profile `constantMassProfile m N = m/(N+1)`, the
ratio is identically `m`, so any positive `m` discharges the
"continuum limit" trivially.

This is the project's **biggest honesty gap** for any external
Clay-grade announcement. `GENUINE_CONTINUUM_DESIGN.md` proposed
three options (A, B, C); Lluis chose **B (document only)** as
interim, with **C (refactor `HasContinuumMassGap` to take a
spacing scheme parameter)** scheduled for "before any external
Clay announcement".

This blueprint **executes Option C strategically**: defines what
a genuine continuum-limit framework looks like, scopes the Lean
work, identifies the mathematical content, and sets up the
scaffolding so Codex (or future Cowork) can implement it.

---

## 1. The mathematical target

A **genuine** continuum-limit predicate must encode:

1. A **physically meaningful lattice-spacing scheme** `a(N)` such
   that `a(N) → 0` as `N → ∞`. Specifically, for asymptotically
   free SU(N_c) Yang-Mills at one-loop:
   ```
   a(g) = (1/Λ) · exp(-1 / (2 b₀ g²))
   ```
   with `b₀ = 11 N_c / (48π²)` (asymptotic freedom coefficient).

2. A **lattice coupling running** `g(N)` such that `g(N) → 0`
   (asymptotic freedom).

3. A **physical mass profile** `m_lat(N)` derived from the
   lattice mass gap at coupling `g(N)`, such that the
   **renormalized mass** `m_lat(N) / a(N)` converges to a
   **positive limit** (this is dimensional transmutation).

The Clay statement requires this convergence to be the spectrum
of an actual quantum mechanical Hamiltonian on the continuum
Hilbert space — but that's the OS/Wightman reconstruction
(Branch III + future). For **Branch VII** we focus on the
predicate-level content: defining the right structure so that
an actual genuine witness can be constructed.

---

## 2. Lean predicate design

### 2.1 `PhysicalLatticeScheme N_c`

Per `GENUINE_CONTINUUM_DESIGN.md` §2:

```lean
namespace YangMills.Continuum

/-- One-loop β-function coefficient for SU(N_c). -/
noncomputable def b0 (N_c : ℕ) : ℝ :=
  (11 : ℝ) * N_c / (48 * Real.pi ^ 2)

/-- A physical lattice-spacing scheme: not just an arbitrary
    positive function of `N`, but one that follows the asymptotic-
    freedom RG scaling of SU(N_c) Yang-Mills. -/
structure PhysicalLatticeScheme (N_c : ℕ) [NeZero N_c] where
  /-- Lattice spacing as function of resolution. -/
  a : ℕ → ℝ
  /-- Strict positivity. -/
  ha_pos : ∀ N, 0 < a N
  /-- Continuum limit: a(N) → 0. -/
  ha_tends_zero : Tendsto a atTop (𝓝 0)
  /-- Lattice coupling. -/
  g : ℕ → ℝ
  /-- Coupling positivity. -/
  hg_pos : ∀ N, 0 < g N
  /-- Asymptotic freedom: g(N) → 0. -/
  hg_asymp_free : Tendsto g atTop (𝓝 0)
  /-- The relation `a(N) = (1/Λ) · exp(-1/(2 b₀ g(N)²))`,
      possibly modulo subleading higher-loop corrections. -/
  ha_g_relation : ∃ Λ : ℝ, 0 < Λ ∧
    Tendsto (fun N => a N * Real.exp (1 / (2 * b0 N_c * (g N)^2)))
      atTop (𝓝 (1 / Λ))

end YangMills.Continuum
```

### 2.2 `HasContinuumMassGap_Genuine`

```lean
/-- Genuine continuum mass gap: the lattice mass `m_lat(N)`
    divided by the physical lattice spacing `scheme.a(N)`
    converges to a positive limit. -/
def HasContinuumMassGap_Genuine
    {N_c : ℕ} [NeZero N_c]
    (scheme : PhysicalLatticeScheme N_c)
    (m_lat : LatticeMassProfile) : Prop :=
  ∃ m_phys : ℝ, 0 < m_phys ∧
    Tendsto (fun N => m_lat N / scheme.a N) atTop (𝓝 m_phys)
```

### 2.3 `ClayYangMillsPhysicalStrong_Genuine`

```lean
def ClayYangMillsPhysicalStrong_Genuine
    {N_c : ℕ} [NeZero N_c] {d : ℕ} [NeZero d]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (scheme : PhysicalLatticeScheme N_c) : Prop :=
  ∃ m_lat : LatticeMassProfile,
    IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat ∧
    HasContinuumMassGap_Genuine scheme m_lat
```

### 2.4 The (non-)projection

The crucial property is that the **existing**
`ClayYangMillsPhysicalStrong` does NOT imply
`ClayYangMillsPhysicalStrong_Genuine` for arbitrary schemes,
because the existing predicate uses the coordinated scaling.

Specifically:

```lean
-- This direction is TRUE:
theorem hasContinuumMassGap_Genuine_implies_existing
    (scheme : PhysicalLatticeScheme N_c) (m_lat : LatticeMassProfile)
    (h : HasContinuumMassGap_Genuine scheme m_lat) :
    HasContinuumMassGap m_lat := by
  -- Need: scheme.a is a valid lattice-spacing function for the
  -- existing definition. This requires generalising the existing
  -- HasContinuumMassGap to take a spacing function as parameter.
  sorry  -- design choice required

-- This direction is FALSE in general:
-- The constantMassProfile witness exhibits that HasContinuumMassGap
-- is satisfiable without any physical scheme, hence there is no
-- implication in the reverse direction.
example : ¬ (∀ m_lat : LatticeMassProfile,
    HasContinuumMassGap m_lat →
    ∀ scheme : PhysicalLatticeScheme N_c,
      HasContinuumMassGap_Genuine scheme m_lat) := by
  sorry  -- counterexample: m_lat = constantMassProfile 1 satisfies
         -- HasContinuumMassGap (via the trick) but does NOT
         -- satisfy HasContinuumMassGap_Genuine for the physical scheme
```

The non-implication direction is **the substantive content**: it
documents that the formal predicate is genuinely weaker than the
genuine one.

### 2.5 What Branch VII produces

A Lean-checkable statement that:

```
v1.93.0+ chain produces ClayYangMillsPhysicalStrong (existing)
                                ↓ NOT IMPLIED by genuine version
ClayYangMillsPhysicalStrong_Genuine (new, requires PhysicalLatticeScheme)
                                ↓ implies (with reconstruction)
Continuum YM with mass gap satisfying OS axioms (Branch III + Wightman)
```

So Branch VII makes the **gap visible at the type level**.

---

## 3. What it would take to produce a witness

Producing
`physical_witness : ClayYangMillsPhysicalStrong_Genuine scheme μ ... `
requires:

### 3.1 An actual `PhysicalLatticeScheme N_c`

Construct the canonical scheme using the lattice β-function
recursion (project's `P6_AsymptoticFreedom` framework):

- `g(N+1) = g(N) - b₀ g(N)³ + O(g⁵)` (one-loop running)
- `a(N+1) = a(N) · exp(-(g(N)² - g(N+1)²) / (2 b₀ · g(N)² · g(N+1)²))`
- `Λ = a(N) · exp(1/(2 b₀ g(N)²))` (the QCD scale, RG-invariant)

This is **ASYMPTOTIC FREEDOM made concrete**. The project has
this framework partially (per
`YangMills/P6_AsymptoticFreedom/BetaFunction.lean`,
`CouplingConvergence.lean`, `AsymptoticFreedomDischarge.lean`) but
the actual `PhysicalLatticeScheme` instance needs to be assembled.

Estimated: ~200 LOC.

### 3.2 A `m_lat` that bounds Wilson correlators uniformly across N

This is the **uniform-in-N lattice mass gap** — the actual hard
content. The F3 chain (Codex's Branch I) gives this **only at
small β**, so the witness only works for `g(N)` in the
small-β regime.

The good news: asymptotic freedom says `g(N) → 0`, so for large
enough `N`, `g(N)` IS in the small-β regime where the F3 chain
applies. So Branch I + Branch VII can combine to give a witness
**for sufficiently large N onward**.

The Branch I output would be:
```lean
∀ β < 1/(28 N_c), ClayYangMillsMassGap N_c at coupling β
```

Composed with Branch VII's running g(N), this gives:
```lean
∃ N₀, ∀ N ≥ N₀, ClayYangMillsMassGap N_c at coupling g(N)
```

with the resulting `m_lat(N)` from the F3 prefactor.

### 3.3 Convergence of `m_lat(N) / a(N)` to a positive limit

This is **dimensional transmutation**. Combining:
- `m_lat(N) ~ kpParameter(g(N)) ~ const · exp(-(...)/g(N)²)` (from F3)
- `a(N) ~ (1/Λ) · exp(-(...)/g(N)²)` (from RG running)
- So `m_lat(N) / a(N) ~ Λ · const`, a **finite, positive constant**.

This is the heart of why Yang-Mills has a finite mass gap in the
continuum even though both `m_lat` and `a` go to zero. The
formalisation needs careful tracking of constants.

Estimated: ~150 LOC (analytic content).

### 3.4 Total scope for the witness

| Component | LOC | Status |
|---|---|---|
| `PhysicalScheme.lean` (predicate definitions) | ~150 | scaffolded by Cowork in Phase 3 |
| `PhysicalScheme_Construction.lean` (concrete scheme) | ~200 | open, requires P6 |
| `M_lat_From_F3.lean` (compose F3 with running coupling) | ~100 | open, requires Branch I closure + Branch VII §3.1 |
| `DimensionalTransmutation.lean` (convergence of ratio) | ~150 | open, requires §3.1, §3.2, §3.3 |
| `ClayYangMillsPhysicalStrong_Genuine.lean` (final assembly) | ~50 | open, glue |
| **Total** | **~650 LOC** | most open |

This is comparable to the F3-Mayer scope (~700 LOC). Substantial
but achievable in a focused effort.

---

## 4. Mathematical references

- Wilson, *Confinement of quarks*, Phys. Rev. D 10 (1974) — original
  lattice gauge theory + RG flow.
- 't Hooft 1972 (unpublished talk; later in many sources) — original
  asymptotic freedom calculation.
- Politzer 1973, Gross-Wilczek 1973 — published asymptotic
  freedom papers.
- Bałaban CMP 109 (1986), 122 (1989) — rigorous RG flow control
  in lattice YM.
- Magnen-Rivasseau-Sénéor *Construction of YM_4 with an infrared
  cutoff*, CMP 155 (1993) — most relevant prior work on
  continuum limit; doesn't fully solve Clay but defines the
  framework.

---

## 5. Risks

| Risk | Likelihood | Mitigation |
|---|---|---|
| The F3 small-β regime `β < 1/(28 N_c)` doesn't extend far enough into the running coupling for the composition to work | medium | Need to verify that `g(N)` actually enters `< 1/(sqrt(28 N_c))` for the relevant `N` range. If not, need to relax the small-β requirement or use Branch II's RG control. |
| Higher-loop corrections to the β-function break the simple scheme structure | low | Mostly subleading; can be absorbed into the `ha_g_relation` field of `PhysicalLatticeScheme`. |
| Mathlib `Tendsto` / `atTop` machinery is incomplete for the constructions needed | low | Mathlib has `Tendsto`, `atTop`, `Filter.Tendsto.div`, `Real.exp` derivatives. Should suffice. |
| The (existing) `HasContinuumMassGap` and the (genuine) version are not properly related | medium | This blueprint flags the non-implication explicitly. The existing predicate is preserved for backwards compat. |

---

## 6. Action items

For Cowork agent (this session, Phase 3):
- [ ] Create `YangMills/L7_Continuum/PhysicalScheme.lean` with
      the `PhysicalLatticeScheme N_c`, `HasContinuumMassGap_Genuine`,
      `ClayYangMillsPhysicalStrong_Genuine` predicate definitions.
      Sorries marking each open obligation. ~150 LOC scaffold.

For Codex (when convenient, after Priority 4.x closure):
- [ ] Implement `PhysicalScheme_Construction.lean` using the
      P6 β-function framework.
- [ ] Implement `M_lat_From_F3.lean` composing F3 output with
      running coupling.
- [ ] Implement `DimensionalTransmutation.lean`.
- [ ] Implement final assembly.

For Lluis (decision pending):
- [ ] Approve Branch VII as a permanent parallel work area for
      Cowork.
- [ ] When approving an external Clay announcement (if ever),
      require that the announcement uses
      `ClayYangMillsPhysicalStrong_Genuine`, not the existing
      coordinated-scaling version.

---

## 7. Summary

Branch VII is the **honesty refactor** of `HasContinuumMassGap`.
It defines a genuine continuum-limit predicate via a physical
lattice-spacing scheme tied to asymptotic freedom. The predicate
is designed to be incompatible with the coordinated-scaling
trick that satisfies the existing `HasContinuumMassGap`
trivially.

This is the **most tractable** of the parallel branches and
should be Cowork's first concrete Lean contribution.

When Codex's Branch I closes (small-β lattice mass gap) and the
P6 asymptotic-freedom framework matures, Branch VII connects
them into a genuine continuum mass gap statement (modulo the
remaining OS reconstruction work in Branch III).

---

*Blueprint complete 2026-04-25 by Cowork agent.*
