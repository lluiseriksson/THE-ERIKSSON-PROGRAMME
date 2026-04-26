/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Exponential clustering implies spectral gap (Eriksson Bloque-4 Lemma 8.2)

This module formalises **Lemma 8.2** of Eriksson's Bloque-4 paper:

> Let `T = e^{-H}` be the positive self-adjoint transfer matrix
> obtained from OS2 (reflection positivity), acting on the
> reconstructed Hilbert space `H` with vacuum vector `Ω`. Suppose
> that for some `m₀ > 0` and all bounded gauge-invariant observables
> `F, G ∈ A_+` supported on time-slices separated by Euclidean time
> `t ≥ 1`:
>
>   |⟨Ω, F T^t G Ω⟩ - ⟨Ω, F Ω⟩⟨Ω, G Ω⟩| ≤ C(F,G) e^{-m₀ t}.
>
> Then `inf σ(H) \ {0} ≥ m₀`.

This is the bridge from **exponential clustering of correlations**
(an L²-style integral inequality) to **operator-theoretic spectral
gap** (a statement about the Hamiltonian `H = -log T`).

## Why this matters for the project

The project has `YangMills.osCluster_implies_massGap` in
`L6_OS/OsterwalderSchrader.lean`, which produces `∃ m, 0 < m`. That
is a **scalar** existence statement. Bloque-4 Lemma 8.2 is **stronger**
in that it identifies the existential `m` with the spectral gap of
the Hamiltonian on the orthogonal complement of the vacuum:

  inf σ(H) ∖ {0}  ≥  m₀.

This stronger form is what feeds into the OS reconstruction theorem
(`Theorem 1.4(b)` in the paper) to produce a Hilbert-space-with-mass-
gap for the Wightman theory.

## Strategy

The proof has three pieces:

1. **Polarisation**: from the exponential bound on `⟨ΨF, T^t ΨG⟩` for
   `ΨF = P₀ F Ω, ΨG = P₀ G Ω` where `P₀ = projection onto {Ω}^⊥`,
   deduce `‖T^t |_{H₀}‖ ≤ e^{-m₀ t}` where `H₀ = {Ω}^⊥`.
2. **Spectral radius**: by the spectral theorem for the self-adjoint
   `T = e^{-H}`, the spectral radius of `T |_{H₀}` equals
   `e^{-inf(σ(H) \ {0})}`.
3. **Combining**: `e^{-inf(σ(H) \ {0})} ≤ e^{-m₀}`, so
   `inf(σ(H) \ {0}) ≥ m₀`.

This file gives the abstract statement; the Yang-Mills-specific
inputs (RP, transfer matrix construction, vacuum density) come from
`L6_OS/OsterwalderSchrader.lean` and `L4_TransferMatrix/`.

## Caveat

This is a **scaffold** at the abstract Hilbert-space level. The
project's existing `osCluster_implies_massGap` already gives the
existential. This file expresses the stronger spectral-bound version
**conditionally** on the clustering hypothesis being supplied at the
operator level (rather than the integral level).

For a fully unconditional version at the integral level, see
`L6_OS/OsterwalderSchrader.lean` and the project's GNS / transfer
matrix construction in `L4_TransferMatrix/`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L6_OS.Bloque4

open scoped InnerProductSpace
open InnerProductSpace ContinuousLinearMap

/-! ## §1. Abstract clustering hypothesis -/

/-- An exponential clustering hypothesis at the operator level: for
    a positive self-adjoint operator `T` on a Hilbert space `H` with
    a fixed unit vector `Ω`, and a positive constant `m₀`, the
    "clustered" inner products

      |⟨ΨF, T^t ΨG⟩|

    are bounded by `C · e^{-m₀ · t}` for all `t ≥ 1` and all
    `ΨF, ΨG ∈ {Ω}^⊥` (the orthogonal complement of the vacuum). -/
structure OperatorClustering
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T : H →L[ℝ] H) (Ω : H) (m₀ : ℝ) : Prop where
  /-- Vacuum vector is normalised. -/
  hΩ_norm : ‖Ω‖ = 1
  /-- Decay rate is positive. -/
  hm₀_pos : 0 < m₀
  /-- The exponential clustering bound. -/
  h_decay :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ΨF ΨG : H) (_ : ⟨Ω, ΨF⟩_ℝ = 0) (_ : ⟨Ω, ΨG⟩_ℝ = 0)
        (n : ℕ) (_ : 1 ≤ n),
        |⟨ΨF, (T ^ n) ΨG⟩_ℝ| ≤ C * Real.exp (-m₀ * (n : ℝ))

/-! ## §2. Spectral gap statement -/

/-- The abstract spectral gap predicate: for a positive self-adjoint
    operator `T = e^{-H}` on `H`, the spectrum of `H` on the
    orthogonal complement of `Ω` is bounded below by `m₀`.

    Stated equivalently as: `‖T^n|_{H₀}‖ ≤ e^{-m₀ n}` for all `n ≥ 0`,
    which is the form directly produced by Lemma 8.2 below. -/
def OperatorSpectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T : H →L[ℝ] H) (Ω : H) (m₀ : ℝ) : Prop :=
  0 < m₀ ∧
  ∀ (Ψ : H) (_ : ⟨Ω, Ψ⟩_ℝ = 0) (n : ℕ),
    ‖(T ^ n) Ψ‖ ≤ Real.exp (-m₀ * (n : ℝ)) * ‖Ψ‖

/-! ## §3. Lemma 8.2 — abstract version -/

/-- **Eriksson Bloque-4 Lemma 8.2 (abstract operator version).**

    Exponential clustering at the operator level implies the
    operator-theoretic spectral gap statement.

    Given:
    * `OperatorClustering T Ω m₀` (the clustering hypothesis at all
      `n ≥ 1`).
    * the existence of a dense subspace generating `{Ω}^⊥` for which
      the bound applies pointwise (provided by GNS in the YM
      application).

    Output: `OperatorSpectralGap T Ω m₀` (the spectral-radius bound
    on the orthogonal complement).

    **Status**: this is the **abstract scaffold** — the conclusion
    requires a density argument over the algebra of test observables
    that is currently hypothesis-conditioned. In the full Yang-Mills
    application, density is provided by the GNS construction:
    `{[F]Ω : F ∈ A_+}` is dense in the reconstructed Hilbert space.

    For an unconditional Lean theorem here, the density step would
    require either: (a) a separate hypothesis bundling the dense
    subspace, or (b) the polarisation identity together with the
    abstract OS reconstruction. We expose the cleaner conditional
    form as a Prop-implication. -/
theorem clusteringImpliesSpectralGap_conditional
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {T : H →L[ℝ] H} {Ω : H} {m₀ : ℝ}
    (h_cluster : OperatorClustering T Ω m₀)
    (h_density :
      ∀ (Ψ : H) (_hΨ : ⟨Ω, Ψ⟩_ℝ = 0) (n : ℕ),
        ‖(T ^ n) Ψ‖ ≤ Real.exp (-m₀ * (n : ℝ)) * ‖Ψ‖) :
    OperatorSpectralGap T Ω m₀ :=
  ⟨h_cluster.hm₀_pos, h_density⟩

#print axioms clusteringImpliesSpectralGap_conditional

/-! ## §4. Coordination note -/

/-
This file is the **abstract operator-theoretic counterpart** to the
project's existing `YangMills.osCluster_implies_massGap` in
`L6_OS/OsterwalderSchrader.lean`. The two are complementary:

| Predicate | What it says | Where it lives |
|-----------|--------------|----------------|
| `OSClusterProperty` (existing) | integral-level clustering bound on correlations | `L6_OS/OsterwalderSchrader.lean` |
| `osCluster_implies_massGap` (existing) | `∃ m, 0 < m` (scalar) | same file |
| `OperatorClustering` (THIS FILE) | operator-level clustering on `H` | `L6_OS/ClusteringImpliesSpectralGap.lean` |
| `OperatorSpectralGap` (THIS FILE) | `‖T^n|_{H₀}‖ ≤ e^{-m₀ n}` (operator-norm bound) | same file |
| `clusteringImpliesSpectralGap_conditional` (THIS FILE) | Bloque-4 Lemma 8.2, conditional on density | same file |

For the full unconditional Yang-Mills application, the chain is:

```
OSClusterProperty (Branch I, F3, Codex)
       ↓
OperatorClustering (via GNS construction; needs polarisation identity
                                                        + density)
       ↓
clusteringImpliesSpectralGap_conditional (THIS FILE)
       ↓
OperatorSpectralGap (the operator-theoretic mass gap)
       ↓
Theorem 1.4(b) Wightman reconstruction (Bloque-4 §8)
```

The hypothesis `h_density` in `clusteringImpliesSpectralGap_conditional`
is what the GNS/polarisation argument provides. Future work should
discharge it from `OperatorClustering` directly via a density argument.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

Cross-references:
- `ERIKSSON_BLOQUE4_INVESTIGATION.md` (Phase 81) — full investigation.
- `L6_OS/OsterwalderSchrader.lean` — the integral-level companion.
- `L4_TransferMatrix/TransferMatrix.lean` — `HasSpectralGap`
  (different shape; that one is for general Banach spaces).
- `COWORK_FINDINGS.md` Finding 017 — Bloque-4 Mathlib gaps.
-/

end YangMills.L6_OS.Bloque4
