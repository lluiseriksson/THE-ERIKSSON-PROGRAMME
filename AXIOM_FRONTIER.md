# Axiom Frontier — THE ERIKSSON PROGRAMME

**Status: v0.8.18-stable · 0 errors · 0 sorrys · 5 axioms**

This document classifies every remaining axiom in `YangMills/P8_PhysicalGap/`:
its mathematical content, what blocks its elimination, and the exact
Mathlib/infrastructure dependency that would allow a proof.

---

## Mathlib gaps (4 axioms)

These are standard theorems known for decades. They will become provable
theorems when Mathlib gains the indicated infrastructure.

---

### `hille_yosida_semigroup`
**File:** `MarkovSemigroupDef.lean`

**Claims:** Every strong Dirichlet form `(E, μ)` generates a Markov semigroup.

**Mathematical status:** Beurling-Deny (1958) / Fukushima (1971) — standard
result of symmetric Dirichlet form theory.

**Blocked by:** Mathlib lacks `C₀`-semigroup theory for unbounded operators:
- Strongly continuous semigroup (`StronglyContSemigroup`) infrastructure
- Resolvent estimates and Hille-Yosida theorem for generators
- Beurling-Deny correspondence: Dirichlet form ↔ Markov semigroup

**Removal plan:**
```lean
-- When Mathlib has:
theorem beurling_deny_semigroup (E : DirichletForm μ) : MarkovSemigroup μ
-- Then: axiom hille_yosida_semigroup → proved theorem
```

**Reference:** Fukushima-Oshima-Takeda, *Dirichlet Forms and Symmetric Markov
Processes*, Theorem 1.3.1.

---

### `lieDerivative_linear`
**File:** `SUN_DirichletForm.lean`

**Claims:** The Lie derivative `∂ᵢ` along generator `Tᵢ` of `su(N)` is linear:
`∂ᵢ(f+g) = ∂ᵢf + ∂ᵢg` and `∂ᵢ(cf) = c·∂ᵢf`.

**Mathematical status:** Trivial consequence of linearity of `deriv`.

**Blocked by:** `lieDerivative` is `opaque` because `SU(N)` lacks:
- `LieGroup` instance (`ModelWithCorners` + `ChartedSpace`) for `Matrix.specialUnitaryGroup`
- `ContMDiff` structure for smooth maps on `SU(N)`
- `HasDerivAt` for the exponential curve `t ↦ U · exp(t · Tᵢ)`

**Removal plan:**
```lean
-- When Mathlib has LieGroup SU(N):
noncomputable def lieDerivative N_c i f U :=
  deriv (fun t => f (U * Matrix.exp (t • lieGenerator N_c i))) 0
-- Then: lieDerivative_linear follows from HasDerivAt linearity
```

---

### `lieDerivative_const`
**File:** `SUN_DirichletForm.lean`

**Claims:** `∂ᵢ(const c) = 0`.

**Mathematical status:** Trivial — derivative of a constant function is zero.

**Blocked by:** Same as `lieDerivative_linear` — `lieDerivative` is opaque.

**Removal plan:** Same as above. With concrete `lieDerivative` via `deriv`,
`deriv_const` from Mathlib gives this immediately.

---

### `sunDirichletForm_contraction`
**File:** `SUN_DirichletForm.lean`

**Claims:** `E(trunc_n f) ≤ E(f)` where `trunc_n(x) = max(min(x,n), -n)`.

**Mathematical status:** Normal contraction property — defining property of
Dirichlet forms (Beurling-Deny criterion).

**Proof route (currently blocked):**
1. `trunc_n` is 1-Lipschitz (provable in Lean via `LipschitzWith`)
2. Chain rule: `∂ᵢ(trunc_n ∘ f)(U) = trunc_n'(f U) · ∂ᵢf(U)` a.e.
3. `|trunc_n'| ≤ 1` → `(∂ᵢ(trunc_n∘f))² ≤ (∂ᵢf)²` pointwise a.e.
4. `integral_mono` + `Finset.sum_le_sum` → `E(trunc_n f) ≤ E(f)`

**Blocked by:** Step 2 requires chain rule for `lieDerivative` — same
dependency as `lieDerivative_linear`.

**Reference:** Fukushima-Oshima-Takeda, Theorem 1.4.1.

---

## Clay core (1 axiom — do not attack)

### `sun_gibbs_dlr_lsi`
**File:** `BalabanToLSI.lean`

**Claims:** SU(N) Yang-Mills satisfies DLR log-Sobolev inequality with constant
`α_star > 0` for all `β ≥ β₀ > 0`.

**Mathematical status:** This IS the mathematical content of the Yang-Mills
mass gap problem. Proving this rigorously is the Millennium Prize.

**Proof strategy (E26 paper series):**
- M1: `Ric_{SU(N)} = N/4` → Haar LSI(N/4) via Bakry-Émery [E26II]
- M2: Polymer expansion bounds → `Σ Dₖ < ∞` cross-scale [E26III, E26V]
- M3: Interface Lemmas → DLR-LSI unconditional [2602.0046, 2602.0073]
- Audit: 29/29 papers pass formal review

**This axiom will not be eliminated by Lean tactics — it requires the full
E26 mathematical programme to be verified.**

---

## Summary

| Axiom | Category | Blocked by |
|-------|----------|------------|
| `hille_yosida_semigroup` | Mathlib gap | `C₀`-semigroup theory |
| `lieDerivative_linear` | Mathlib gap | `LieGroup SU(N)` |
| `lieDerivative_const` | Mathlib gap | `LieGroup SU(N)` |
| `sunDirichletForm_contraction` | Mathlib gap | Chain rule on Lie groups |
| `sun_gibbs_dlr_lsi` | Clay core | Yang-Mills E26 programme |

**When `LieGroup SU(N)` lands in Mathlib:** 3 axioms eliminated at once
(`lieDerivative_linear`, `lieDerivative_const`, `sunDirichletForm_contraction`).

**When `C₀`-semigroup theory lands in Mathlib:** `hille_yosida_semigroup` eliminated.

**When E26 is fully verified:** `sun_gibbs_dlr_lsi` eliminated → P8 complete.
