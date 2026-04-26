# ERIKSSON_BLOQUE4_INVESTIGATION.md

**Author**: Cowork agent (Claude)
**Date**: 2026-04-25 (Phase 81)
**Subject**: structured investigation of `YangMills-Bloque4.pdf` (Eriksson
2026, "Exponential Clustering and Mass Gap for Four-Dimensional SU(N)
Lattice Yang–Mills Theory") cross-referenced with Mathlib's current
infrastructure, to surface creative angles for Cowork's contribution.

---

## 0. TL;DR

The Bloque-4 paper assembles **three pillars** to prove the lattice
mass gap:

1. **Balaban's RG framework** (CMP 1984–1989, black-boxed).
2. **Terminal cluster expansion** (Eriksson Paper [1], the F3 chain).
3. **Multiscale correlator decoupling** (this paper, §6 — the new
   contribution).

Plus **§4 Coupling Control** — the Cauchy-bound argument that closes
the inductive RG.

The paper achieves OS0, OS2, OS3, OS4 + vacuum uniqueness +
non-triviality, but **does NOT prove OS1** (full O(4) Euclidean
covariance). Theorem 1.4(c) is conditional on O(4) covariance
holding in the continuum limit.

This investigation surfaces **5 concrete Mathlib / Lean gaps** that
Cowork could plausibly contribute toward closing, ordered by
tractability.

---

## 1. The paper's three-pillar structure

```
                      Balaban's RG (CMP 1984-1989)
                             │
                             ▼
                  effective terminal measure µa∗
                             │
                             ▼
              Terminal KP bound (Paper [1])
                             │
                             ▼
        Terminal exp. clustering (Theorem 5.5)
                             │
                             │   <─── Multiscale telescoping
                             │        (Prop 6.1, the NEW idea)
                             ▼
              Mass gap on η-lattice (Theorem 7.1)
                             │
                             ▼
                  OS0 + OS2 + OS3 + OS4 (§8)
                             │
                             │   <─── conditional on O(4) (OS1)
                             ▼
                  Wightman QFT (Theorem 1.4(c))
```

The **Coupling Control** argument (§4) is what makes the whole RG
chain self-consistent — it closes the assumption `g_k ∈ (0, γ]` that
Balaban's results require.

---

## 2. Mathlib gaps surfaced by Bloque-4

### Gap 1: Law of Total Covariance (LTC)

**Status**: not in Mathlib (verified by grep on
`Mathlib/Probability/`).

**Statement**: for σ-algebras `F ⊂ G` and integrable `X, Y`:
```
Cov(X, Y | F) = E[Cov(X, Y | G) | F] + Cov(E[X | G], E[Y | G] | F).
```

**Used in**: Eriksson Bloque-4, Proposition 6.1 (telescoping
identity along `σ_a₀ ⊃ σ_a₁ ⊃ ⋯ ⊃ σ_a_*`).

**Tractability**: Mathlib has `condExp` (conditional expectation),
`Variance.cov` (covariance), tower property
(`condExp_condExp_of_le`). LTC is straightforward from these.
Estimated effort: ~80 LOC + Mathlib PR.

**Strategic value**: HIGH. LTC is a fundamental probability theorem
that should be in Mathlib regardless of this project. Once landed,
the project's multiscale telescoping becomes a clean application.

### Gap 2: Cauchy estimate on the β-function

**Status**: Mathlib has Cauchy's estimate
(`Complex.abs_deriv_le_aux`, `Complex.derivWithin_eq`,
`Differentiable.deriv`). What's missing is the *application* to the
discrete RG β-function.

**Statement**: if `f : ℂ → ℂ` is analytic on `|z| < R` and `f(0) = b₀`,
then `|f(z) - b₀| ≤ M·|z|/R` for `|z|` small, where
`M = sup_{|w| ≤ R} |f(w) - b₀|`.

**Used in**: Eriksson Bloque-4, Proposition 4.1 (Coupling Control).

**Tractability**: MEDIUM. Cauchy estimates are in Mathlib; the
application is structural. The harder content is the analyticity of
the β-function itself (Balaban's Theorem 1, [6]), which is *not*
in Mathlib and requires substantial gauge-theoretic infrastructure.

**Strategic value**: MEDIUM. The abstract Cauchy-bound chain is
straightforward; the analyticity of the β-function is what's hard.
Cowork could formalize the abstract chain; the analyticity itself
remains a Branch II obligation.

### Gap 3: Klarner / Lattice Animal Bound

**Status**: not in Mathlib. The bound `count(connected polymers of
size n containing origin in d-D) ≤ (2de)^n` is Madras-Slade
(Self-Avoiding Walk, 1993). Codex is working on this in
`YangMills/ClayCore/LatticeAnimalCount.lean` (Priority 1.2).

**Statement** (Lemma C.1 in Bloque-4): for `κ > log(2de)`,
```
∑_{X ∋ 0, X connected} e^{-κ d(X)} < ∞.
```

**Used in**: Bloque-4 §5.2 (oscillation bound), §5.3 (terminal cluster
sum), §A (KP ⇒ exp decay).

**Tractability**: HARD. This is genuine combinatorial work.

**Strategic value**: HIGH (substantively). Codex's primary
focus.

### Gap 4: KP convergence ⇒ exponential decay (Proposition A.1)

**Status**: not in Mathlib. This is the abstract polymer-model
exponential clustering result.

**Statement**: for a hard-core polymer gas with KP-bounded activities,
truncated correlations decay exponentially in spatial separation.

**Used in**: Bloque-4 Theorem 5.5 + Theorem 7.1 (terminal clustering).

**Tractability**: MEDIUM. Standard cluster-expansion theory; Codex's
F3-Mayer chain is on this path.

**Strategic value**: HIGH. Branch I terminus.

### Gap 5: Spectral gap from exponential clustering (Lemma 8.2)

**Status**: partially in the project (`infiniteVolume_OS_massGap`
gives `∃ m, 0 < m`). Bloque-4 Lemma 8.2 is stronger: it gives
`inf σ(H) \ {0} ≥ m₀` for the transfer-matrix Hamiltonian.

**Statement**: given OS2 (RP) and exponential clustering with rate
`m₀`, the transfer matrix `T = e^{-H}` has spectral gap `≥ m₀` on
the orthogonal complement of the vacuum.

**Used in**: Bloque-4 §8 (OS reconstruction with mass gap).

**Tractability**: MEDIUM. Mathlib has spectral theory for
self-adjoint operators (`ContinuousLinearMap.spectrum`,
`InnerProductSpace.spectralRadius`). The polarization +
density argument is standard.

**Strategic value**: MEDIUM. Closes the gap from
correlation-decay-style mass gap to operator-theoretic spectral gap.

---

## 3. Creative angles where Cowork can contribute

Ordered by strategic value × tractability:

### 3.1 Highest-value: formalize **Law of Total Covariance** in Mathlib

The LTC is:
* fundamental probability,
* not in Mathlib (verified),
* directly used in Bloque-4 Prop 6.1,
* tractable from existing Mathlib infrastructure.

A successful Mathlib PR would:
* benefit the broader Mathlib community,
* make the project's multiscale-telescoping argument formalizable,
* serve as a model for the next iteration of Cowork's work on
  Bloque-4.

**Sketch**:
```lean
theorem cov_eq_cond_cov_add_cov_cond_exp
    {Ω : Type*} {m mF mG : MeasurableSpace Ω}
    (hF : mF ≤ mG) (hG : mG ≤ m)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : Ω → ℝ)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : Integrable (X * Y) μ) :
    cov mF μ X Y =
      μ[cov mG μ X Y | mF] +
      cov mF μ (μ[X | mG]) (μ[Y | mG]) := by
  -- Standard proof via tower property + bilinearity of covariance.
  sorry
```

### 3.2 Second-highest: formalize **Lemma 8.2** (clustering ⇒ spectral gap)

The lemma is operator-theoretic, fits Mathlib's spectral-theory
infrastructure, and bridges a gap in the project's current
"mass gap" formulations (which prove `∃ m > 0` rather than
`inf σ ≥ m_0`).

### 3.3 Documentation: Eriksson Bloque-4 ↔ project predicate map

A document that maps each lemma / theorem / proposition in
Bloque-4 to the corresponding Lean predicate / theorem / structure
in the project. Useful for cross-referencing during proof work.

### 3.4 Update OPENING_TREE.md with the multiscale-decoupling branch

The project's `OPENING_TREE.md` has 7 branches (I–VII). Bloque-4 §6
(multiscale correlator decoupling) is essentially a NEW branch that
reduces the η-lattice mass gap to the terminal-scale mass gap
plus UV-scale errors. This deserves explicit recognition.

### 3.5 Document the OS1 caveat

Even Eriksson's Bloque-4 paper does NOT prove OS1 (full O(4)
covariance). The project's claim of "Clay literal closure" must
make this explicit. `KNOWN_ISSUES.md` should mention OS1 as the
**single uncrossed barrier between lattice mass gap and Wightman
QFT**.

---

## 4. The OS1 caveat — strategic implication

Per Bloque-4 Theorem 1.4(c), full Wightman QFT is **conditional on
O(4) covariance in the continuum limit**. This is a separate
mathematical question (rotational symmetry restoration), not part
of the Balaban / KP / multiscale-decoupling framework.

**Implication for the project**:

* The current ladder
  `ClayYangMillsMassGap → ClayYangMillsPhysicalStrong →
   ClayYangMillsPhysicalStrong_Genuine` does not cleanly capture
  the OS1 caveat.
* A future predicate `ClayYangMillsWightman` would require:
  (a) all of `ClayYangMillsPhysicalStrong_Genuine`, plus
  (b) full O(4) Euclidean covariance of the continuum limit.
* The literal Clay Millennium statement is `ClayYangMillsWightman`,
  not `ClayYangMillsPhysicalStrong_Genuine`.

This justifies the project's `~12 %` literal-Clay estimate
(`README.md` §2 strict-Clay row): even if Branches I + II close,
OS1 remains.

---

## 5. Mathlib infrastructure already available (positive findings)

The paper uses:

* `Real.exp` and its properties — fully in Mathlib.
* Cauchy estimates for analytic functions — fully in Mathlib.
* Conditional expectations — `Mathlib.Probability.ConditionalExpectation`.
* Spectral theory for self-adjoint operators —
  `Mathlib.Analysis.InnerProductSpace.Spectrum`.
* Lattice combinatorics (sums over subsets, etc.) — fully in Mathlib.
* `Real.log` and asymptotic-freedom-style estimates — partially in
  Mathlib.

So the **infrastructural prerequisites** for formalizing Bloque-4
exist; the gaps are at the integration / domain-specific layer
(LTC, β-function analyticity, polymer-cluster theory, etc.).

---

## 6. Recommended action items for next session

1. **PRIORITY 1 (HIGH-VALUE, TRACTABLE)**: draft Mathlib PR for the
   Law of Total Covariance. Estimated 80 LOC + standard tower-property
   proof.

2. **PRIORITY 2 (STRUCTURAL CLARITY)**: formalize Lemma 8.2 in
   Lean using Mathlib's spectral-theory infrastructure. Bridges
   the project's `infiniteVolume_OS_massGap` to a stronger
   `inf σ(H) \ {0} ≥ m_0` statement.

3. **PRIORITY 3 (DOC-LEVEL)**: write `BLUEPRINT_MultiscaleDecoupling.md`
   complementing the existing `BLUEPRINT_BalabanRG.md` and
   `BLUEPRINT_F3Count.md`. Captures Bloque-4 §6 as a project
   blueprint.

4. **PRIORITY 4 (STATUS-LEVEL)**: update `OPENING_TREE.md` with
   the multiscale-decoupling branch and the OS1 caveat.

5. **PRIORITY 5 (HOUSEKEEPING)**: cross-reference Bloque-4
   theorems with project predicates in a single map document.

---

## 7. Closing remarks

The Bloque-4 paper is **the strategic centerpiece** for
understanding the project's current trajectory. Its three-pillar
structure (Balaban + KP + Multiscale Decoupling) directly maps to
the project's three branches (Codex BalabanRG/, F3 chain, and an
implicit "multiscale" layer that has not yet been explicitly
captured).

Cowork's most strategic immediate contribution is to **make the
multiscale-decoupling pillar explicit** in the project's Lean
infrastructure, complementing Codex's BalabanRG/ and F3 work. The
LTC formalization (§3.1) is the natural starting point.

---

*Investigation complete 2026-04-25 evening (Phase 81) by Cowork agent.
Cross-referenced with `YangMills-Bloque4.pdf` (Eriksson 2026,
February release). See `COWORK_FINDINGS.md` Findings 015 + 016 for
the parallel late-session structural-triviality observations on
Codex's BalabanRG/ infrastructure.*
