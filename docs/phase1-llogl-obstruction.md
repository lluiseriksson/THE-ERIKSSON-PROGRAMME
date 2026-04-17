# Phase 1 — The L·log·L Obstruction

**Date:** 2026-04-17
**Commit:** `41cc169`
**Branch:** `docs/phase1-llogl-obstruction`
**Scope:** documentation only; no `.lean` files are modified; no sorries or axioms are introduced.

---

## 1. Status

The project currently contains exactly one `sorry`, located at

```
YangMills/P8_PhysicalGap/BalabanToLSI.lean:805
```

The reduction kernel `#print axioms clay_millennium_yangMills` therefore includes
`sorryAx` in its oracle set (in addition to `propext`, `Classical.choice`,
`Quot.sound`). Zero project-introduced named axioms; one `sorry` remains.

The count progression `3 → 2 → 1` recorded in commits `7d7a5d8`, `d6072ad`,
`41cc169` was a **refactor**: the L·log·L integrability hypothesis was threaded
upward through `integrable_f2_mul_log_f2_div_haar` and
`integrable_f2_mul_log_f2_haar`, concentrating the gap at a single call site
rather than closing it. The underlying mathematical obstruction is unchanged.

**Scope note.** Closing the line-805 sorry in a sound way is not a local
repair. The placeholder `sunDirichletForm` (§4) makes the current proof of
`sun_haar_lsi` algebraically tautological; any genuine L·log·L input forces a
refactor of the LSI chain onto `sunDirichletForm_concrete` and a real
Bakry–Émery reproof. The L·log·L envelope lemma (see §7, item 4) is the only
piece of this program that can be written in isolation.

## 2. What the sorry asserts

The `have` binding at line 805 is, verbatim:

```lean
have hint_haar_log :
    MeasureTheory.Integrable
      (fun x => f x ^ 2 * Real.log (f x ^ 2))
      (sunHaarProb N_c) := sorry
```

Context at the call site (inside `lsi_normalized_gibbs_from_haar_of_ent_pert`,
signature at lines 717–731):

- `N_c : ℕ`, `[NeZero N_c]`, `hN_c : 2 ≤ N_c`;
- `β α : ℝ` with `hβ : 0 < β`, `hα : 0 < α`;
- `f : SUN_State N_c → ℝ` with `hf : Measurable f`;
- `hint_f2 : MeasureTheory.Integrable (fun x => f x ^ 2) (sunHaarProb N_c)`;
- the log-Sobolev hypothesis for Haar (tautological under the placeholder
  Dirichlet form; see §4):

  ```lean
  (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α)
  ```

- `_hProb : IsProbabilityMeasure ((sunHaarProb N_c).withDensity …)`;
- `hEntPert`, an entropy-perturbation hypothesis quantified over arbitrary
  measurable `f`, which is itself discharged by the same L·log·L branch;
- `hpos : 0 < ∫ x, f x ^ 2 ∂(sunHaarProb N_c)`.

No Dirichlet-energy hypothesis on `f` and no L^p bound for any `p > 2` are in
scope. From this hypothesis set alone, `hint_haar_log` cannot be derived.

## 3. Why it is hard

The statement `f² ∈ L¹(μ) ⇒ f²·log(f²) ∈ L¹(μ)` is false on any finite measure
space that admits a countable collection of pairwise disjoint measurable sets of
arbitrarily small positive measure. The compact Haar measure on `SU(N)` satisfies
this (`N_c ≥ 1`). A concrete counterexample on any such space is:

- Choose disjoint measurable sets `E_n` with `μ(E_n) = C / (n² · (log n)²)`,
  `n ≥ 2`, with `C` chosen so `∑ μ(E_n) ≤ μ(Ω)`.
- Define `f² = n` on `E_n` and `0` elsewhere.
- Then `∫ f² dμ = C · ∑ 1 / (n · (log n)²) < ∞` (convergent by Bertrand's
  series test: `∑ 1/(n · (log n)^s)` converges iff `s > 1`).
- But `∫ f² · log(f²) dμ = C · ∑ log n / (n · (log n)²) = C · ∑ 1 / (n · log n) = ∞`
  (divergent by the same test with `s = 1`).

Hence `L¹(f²) ⊄ L¹(f²·log f²)` and no Bochner / Lebesgue manipulation can
bridge the gap without a strictly stronger regularity input.

The standard ways to close the gap all require input that is not present at the
call site:

- **Sobolev embedding.** `H¹(SU(N)) ↪ L^p` for some `p > 2`, then
  `L^p ⊂ L·log·L` on a finite measure. Requires a Dirichlet-energy hypothesis
  on `f` (see §6 and §7).
- **Gaussian / Bakry-Émery LSI applied to `|f|`.** Requires the genuine
  gradient-squared Dirichlet form in scope (see §4).
- **Direct bound by a known integrable envelope.** Requires an `L^∞` or `L^p`
  bound on `f` at the call site.

None of these inputs is available through the chain of hypotheses threaded into
`lsi_normalized_gibbs_from_haar_of_ent_pert`.

## 4. Attempts that failed

Four distinct strategies were evaluated in prior phases and rejected:

1. **`Integrable.mul` of `f²` against `Real.log (f x ^ 2)`.** Requires
   boundedness of `log (f²)`, which fails on the null set where `f = 0` (log →
   −∞) and on any region where `|f|` is large.

2. **Truncation + DCT.** Constructing `f_N = f · 𝟙_{|f|≤N}` gives pointwise
   `f_N² · log f_N² → f² · log f²`, but the dominated-convergence majorant
   still requires `f² · |log f²| ∈ L¹`, which is what we are trying to prove.

3. **Symmetric collapse of `entSq`.** `entSq` is defined as a difference
   `∫ f²·log f² dμ − (∫ f² dμ) · log(∫ f² dμ)`. If the first term is
   non-integrable, the Bochner convention assigns it `0`, so `entSq` collapses
   to `−μ(f²) · log μ(f²)` on the non-integrable branch. This collapsed value
   does not match the value produced by the integrable branch on the same
   `μ(f²)`, so any downstream step that treats `entSq` as a single function of
   `f` (i.e., that does not branch on integrability) fails.

4. **Algebraic closure via `sunDirichletForm` (definition used by the Clay
   chain).** The definition at `BalabanToLSI.lean:35` is

   ```lean
   noncomputable def sunDirichletForm (N_c : ℕ) [NeZero N_c]
       (f : SUN_State N_c → ℝ) : ℝ :=
     (N_c : ℝ) / 8 *
       (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(sunHaarProb N_c)
         − (∫ x, f x ^ 2 ∂(sunHaarProb N_c))
           * Real.log (∫ x, f x ^ 2 ∂(sunHaarProb N_c)))
   ```

   This is `(N_c / 8) · entSq(sunHaarProb, f)` — a placeholder, not a
   Dirichlet form. The geometric gradient-squared form is defined separately
   as `sunDirichletForm_concrete` (`SUN_DirichletCore.lean:31`,
   `∑_i ∫ (lieDerivative i f)² dμ`), but is not used in the LSI chain. Under
   the placeholder definition, `hHaar` reduces algebraically to
   `entSq ≤ entSq` (see `sun_haar_lsi` and `bakry_emery_lsi := id` at
   `BalabanToLSI.lean:314–340`), so it carries no regularity on `f`. The
   hypothesis `sunDirichletForm f < ∞` therefore provides no regularity that
   would imply `f² · log f² ∈ L¹`.

## 5. The wrong-axiom trap

It is tempting to posit a named axiom of the shape

> `Integrable (fun x => f x ^ 2) μ → Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ`

on a finite measure `μ`. This axiom is **mathematically false** (§3
counterexample). Adopting it as a project axiom would convert a `sorry` into a
`#print axioms`-visible but unsound hypothesis.

A weaker shape that still avoids the real work — for example, requiring only
`Measurable f` and `∫ f² < ∞` — has the same counterexample. Any shape that
genuinely implies L·log·L integrability must carry a strictly stronger
regularity premise (`MemLp f p` for some `p > 2`, or a Dirichlet-energy bound).
At that point, the axiom is either (a) a trivial consequence of Mathlib's
`MemLp.mono_exponent` plus the envelope bound `x² · |log x²| ≤ C (1 + |x|^p)`
— i.e., not a new axiom but a small lemma — or (b) a statement equivalent to
the compact-manifold Sobolev embedding, which is not an axiom but a theorem to
be proved.

In other words: the wrong-axiom trap is to launder the Sobolev theorem into an
assumption by dropping its Dirichlet-energy hypothesis. The project does not
take this path.

## 6. The correct closing theorem

The mathematically correct replacement for the sorry is a lemma of the form:

```lean
theorem integrable_sq_mul_log_sq_of_dirichlet_bound
    {N_c : ℕ} [NeZero N_c]
    {f : SUN_State N_c → ℝ}
    (hf : Measurable f)
    (hf2 : MeasureTheory.Integrable (fun x => f x ^ 2) (sunHaarProb N_c))
    (M : ℝ)
    (hD : sunDirichletForm_concrete N_c f ≤ M) :
    MeasureTheory.Integrable
      (fun x => f x ^ 2 * Real.log (f x ^ 2))
      (sunHaarProb N_c)
```

Note: `SUN_State N_c` is an `abbrev` for `SUN_State_Concrete N_c`
(`BalabanToLSI.lean:33`), so `f : SUN_State N_c → ℝ` matches
`sunDirichletForm_concrete`'s argument type definitionally.

The hypothesis `hD` is an explicit Dirichlet-energy bound; on a compact
Riemannian manifold with dimension `n = N² − 1 ≥ 3`, the Sobolev embedding
`H¹ ↪ L^{2n/(n−2)}` followed by `L^p ⊂ L·log·L` for `p > 2` on a finite measure
gives the conclusion, with the downstream L·log·L constant depending on `M` via
the Sobolev constant. For `N = 2` (`n = 3`) the critical Sobolev exponent is
`6`; for `N = 3` (`n = 8`) it is `8/3`; both exceed `2`, so the argument works
for all physically relevant `N ≥ 2`.

To use this lemma at line 805, the call site's hypothesis set must carry `hD`
(with some explicit `M`), which today it does not. That is part of the
refactor in §7.

## 7. What a real closure would require

Closing the sorry via the Sobolev route (Option A, long-term) requires all of
the following ingredients, none of which are presently in Mathlib or the
project:

1. **Lie / Riemannian structure on `SU(N)`.** A bi-invariant Riemannian metric
   with explicit Ricci lower bound; `LieGroup` instance; chart cover.
2. **Sobolev space `H¹(SU(N))`.** Either via weak derivatives along
   left-invariant vector fields, or via chart-based Sobolev spaces glued.
3. **Compact-manifold Gagliardo–Nirenberg–Sobolev.**
   `H¹(SU(N)) ↪ L^{2n/(n−2)}` with constant depending only on the metric.
4. **L^p → L·log·L envelope lemma on a finite measure.** A `MemLp` → L·log·L
   lemma (the one piece that is pure Mathlib-level real analysis and is safe
   to build in isolation).
5. **Refactor of `sunDirichletForm` to `sunDirichletForm_concrete`** throughout
   the LSI chain, and **genuine reproof of `sun_haar_lsi`** via Bakry–Émery
   with a real Ricci lower bound. The current proof of `sun_haar_lsi` is
   algebraically tautological under the placeholder definition; any sound
   closure of the sorry forces the chain to be re-established with the
   geometric Dirichlet form.

The smallest atomic piece of this program that is safe to formalize
independently is item (4), `memLp_gt_two_integrable_sq_mul_log_sq` on a general
finite measure space: genuine Mathlib-level real analysis, useful regardless of
which macro-strategy is eventually chosen, and ~80–150 lines of Lean.

## 8. Pointers

- `YangMills/P8_PhysicalGap/BalabanToLSI.lean:805` — the sorry
- `YangMills/P8_PhysicalGap/BalabanToLSI.lean:33` — `abbrev SUN_State := SUN_State_Concrete`
- `YangMills/P8_PhysicalGap/BalabanToLSI.lean:35` — `sunDirichletForm`
  (placeholder; used by the Clay chain)
- `YangMills/P8_PhysicalGap/SUN_DirichletCore.lean:31` —
  `sunDirichletForm_concrete` (geometric; not used by the Clay chain)
- `YangMills/P8_PhysicalGap/BalabanToLSI.lean:314–340` — tautological
  `BakryEmeryCD` and `sun_haar_lsi`
- `YangMills/P8_PhysicalGap/BalabanToLSI.lean:717–731` —
  `lsi_normalized_gibbs_from_haar_of_ent_pert` signature
- `AXIOM_FRONTIER.md` (v0.35.0 section, same commit) — authoritative listing of
  the current obstruction
- `HYPOTHESIS_FRONTIER.md` — user-facing hypothesis ledger
- `PHASE8_SUMMARY.md` — stale; retained with an obsolescence header, not
  updated
- viXra paper [45] ("Uniform Log-Sobolev Inequality and Mass Gap for Lattice
  Yang–Mills Theory") — external writeup; its claims are stronger than the
  formalization presently supports. This document is the reconciliation point.
- Mathlib 4 `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:118` —
  `MemLp.mono_exponent` (ingredient for item (4) of §7)
- Commit `41cc169` — most recent sorry-reduction refactor (threading, not
  closure)
