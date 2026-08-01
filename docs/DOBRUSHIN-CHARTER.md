# DOBRUSHIN CHARTER — "The wall was in the wrong place":
# volume-uniform clustering for the COUPLED spatial kernel,
# by a coupling argument rather than a spectral one.
#
# Registered 2026-08-01, BEFORE any fabrication in this lane.

## Why this lane exists

The S block proved its uniform statements with **Schur's test on constant row
sums** (`YangMills/OS/SpatialUniform.lean`).  At nonzero spatial coupling the
row sums stop being constant — that is `coupled_rowSums_not_constant`
(`YangMills/OS/SpatialExtent.lean:205`), proved on a two-site witness, and it is
labelled THE OBSTRUCTION in that module.

**It is an obstruction to the METHOD, not to the theorem.**  The claim "the
weight destroys uniformity" was already retracted of record (ledger Addendum
561) as unproved; what survived was a measurement of degeneracy.  This lane
opens because the retracted claim kept selecting targets anyway.

## Correction of record, entered before any work

An earlier reading of this desk asserted that `ReflectionSplitting`
(`YangMills/OS/ReflectionSplitting.lean:74`) could be instantiated directly by
the paper-13 producer (`bondEquiv`, `gibbsWeight_joinBond`).  **That is wrong as
stated and is withdrawn here.**  `ReflectionSplitting` is indexed by
`GaugeData N Edge Plaq`, whose `boltz` is `∏ p, weight (hol p)` with ONE weight
function `weight : ZMod N → ℝ` shared by every plaquette.  The S block's slice
weight `w` is an arbitrary positive function of a whole slice, and even when it
factorises over spatial bonds the model is ANISOTROPIC (`β ≠ γ`), which the
single shared `weight` field cannot express.

The connection therefore needs one generalisation first —
`weight : Plaq → ZMod N → ℝ` — and that generalisation is a separate brick,
registered here as D-0 and NOT claimed as free.

## The target

For the coupled kernel of the S block, symmetrised,

    T_L(σ,τ) = √(w_γ(σ)) · K_β(σ,τ) · √(w_γ(τ)),
    K_β(σ,τ) = ∏_j z2Bond β (σ_j) (τ_j),
    w_γ(σ)   = ∏_j z2Bond γ (σ_j) (σ_{j+1}),

prove `specRatio(T_L) ≤ ρ < 1` with `ρ` INDEPENDENT of `L`, on an explicit
non-empty window of `(β,γ)`.

The consumer already exists and was verified by elaboration on this branch:

    volumeUniform_gap   (YangMills/OS/TransferGap.lean:546)
      (∀ i, ∀ v, ∃ C, ∀ n, |connCorr (T i) (Ω i) v n| ≤ C * r ^ n) → …
      → ∃ m, 0 < m ∧ ∀ i, ‖projectedTransfer (T i) (Ω i)‖ ≤ exp (-m)

Note the quantifier order, which is load-bearing and is the reason this lane is
possible at all: **`C` may depend on the volume `i` and on `v`; only `r` is
common.**  The lane's own standing objection — "a bound `C(L)·ρ^N` with
`C(L)→∞` says nothing" (`SpatialUniform.lean`) — does not apply to this
consumer, because its conclusion is an operator-norm bound.

## The ladder, and what each rung alone is worth

* **D-1 — the Dobrushin matrix lemma (pure linear algebra, no probability).**
  For `C : ι → ι → ℝ`, `C ≥ 0`, `C i j = 0` whenever `dist i j > 1`, and
  `∀ i, ∑ j, C i j ≤ α < 1`:  `∑_n (C^n) i j ≤ α ^ (dist i j) / (1 - α)`.
  This is where volume-freeness comes from, and it is a self-contained,
  reusable brick.  **Worth alone: a library lemma, nothing more.  No physics
  claim may be attached to D-1.**
* **D-2 — the Dobrushin coefficient of the S-block cell**, `C_ij = tanh|J_ij|`,
  and the explicit window `2 tanh β + 2 tanh γ < 1`.
* **D-3 — comparison ⇒ exponential decay of connected correlations**, rate
  free of `L` and `N`.  This is THE bottleneck; everything else is assembly.
* **D-4 — transport to `connCorr`** through the paper-9 identification.
* **D-5 — `volumeUniform_gap` ⇒ the uniform `specRatio` bound.**

## PRE-REGISTERED JUDGES

`scripts/judge_dobrushin.py`, committed in this same commit, BEFORE a line of
Lean.  Every gate exits NON-ZERO on failure — a gate that cannot fail a CI is a
report, not a gate (paper-12 lesson).  Gates are SEPARATE: no gate bundles a
theorem with its witness (Addendum 548 / paper-12 gate B lesson).

* **J1 — phase localisation.**  Pre-registered cells.  For every cell with
  `sinh2β·sinh2γ < 1`: the Aitken limit of `r(L)` must be `≤ 0.95` and the
  increment ratio `< 1` (saturation).  For every cell with `sinh2β·sinh2γ > 1`:
  `r(12) ≥ 0.99`.  **Licenses the claim that the degeneracy is a property of
  the ORDERED phase and not of the weight.**
* **J2 — D-1 predicted as a NUMBER, not sampled.**  Deterministic matrices on a
  path and on a grid; `∑_n (C^n) i j` computed to convergence and compared
  against `α^dist/(1-α)` at `1e-12`.  **Licenses fabricating D-1.**
* **J3 — the window is non-empty AND conservative.**  Every grid point with
  `2tanh β + 2tanh γ < 1` must satisfy `sinh2β·sinh2γ < 1`, and both sets must
  be non-empty.  **Licenses calling the window explicit and non-sharp.**  If a
  Dobrushin point fell outside the Onsager region this gate FAILS and the
  interpretation of the whole lane changes.

## PROHIBITIONS (registered, self-audited before any commit)

1. The word **clustering** is not used for an infinite-volume statement; no
   infinite-volume state is constructed in this lane.
2. The window is never called **sharp**.  Onsager's line is the true boundary
   and the Dobrushin window is strictly inside it.
3. No consequence for Yang–Mills is stated, suggested, or implied.
4. Dobrushin's theorem is **classical**.  Nothing in this lane may be presented
   as new mathematics; what is new is the mechanisation, the explicit constant,
   and the fact that it closes a registered open wall of this corpus.
5. No claim of "delivered" without an external verdict (C6 Amendment-2 lesson).

## ROLES

This session FABRICATES.  It does not audit itself.  The five-role audit and
any external verdict are a different desk, per CLAUDE.md Part I §4.

## STAGING

Explicit paths only.  `git add -A` is forbidden while other desks share this
clone; `p39.py`, `p40.py` and `scripts/__pycache__/` are other desks' untracked
files and are not this lane's to commit.
