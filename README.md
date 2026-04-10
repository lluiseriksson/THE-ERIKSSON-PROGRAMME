# The Eriksson Programme: Machine-Verified Yang–Mills Mass Gap

## What This Is

A long-term Lean 4 formalization project targeting the **Yang–Mills existence and mass gap problem**. The goal is to reduce the problem to the smallest possible set of explicitly-stated, machine-checked hypotheses.

**Current tag**: v1.18.0 (Campaign C102 complete)
**Lean**: 4.29.0-rc6 · **Mathlib**: current · **Lake**: 5.0.0-src

## Two Targets: Vacuous vs. Non-Vacuous

A critical discovery (C72, v0.88.0): both `ClayYangMillsTheorem` and `ClayYangMillsStrong` are **vacuously provable** via trivial witnesses. They remain in the codebase but are **not the genuine goal**.

The genuine, non-vacuous target is:

```
ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP
```

This asserts **exponential decay of connected correlators**:

> ∀ N p q, |W_cc(N,p,q)| ≤ C · exp(−γ · distP N p q)

where W_cc is the Wilson connected correlator and γ > 0 is the mass gap.

## Honest Progress Assessment

- `ClayYangMillsTheorem` / `ClayYangMillsStrong`: **100% formalized but vacuous**
- `ClayYangMillsPhysicalStrong` (genuine target): **∼19% complete**
  - The formal chain from 4 hypotheses to the conclusion is complete (P8_PhysicalGap)
  - The 3 core physics hypotheses remain unproven
  - `FeynmanKacFormula` is the deepest gap (requires Balaban RG machinery)

## Live Path Hypotheses (4 as of v1.18.0)

| # | Hypothesis | Description |
|---|-----------|-------------|
| 1 | `FeynmanKacFormula` | FK transfer-matrix representation of W_cc |
| 2 | `StateNormBound` | ‖ψ_obs N p‖ ≤ C_ψ (uniform state norm bound) |
| 3 | `HasSpectralGap T P₀ γ C` | Spectral gap of the transfer matrix |
| 4 | `hdistP` | 0 ≤ distP N p q (distance non-negativity) |

C102 eliminated `FeynmanKacOpNormBound` via Cauchy-Schwarz (derived from FK + StateNorm).
C103 (in progress) will chain to prove `ClayYangMillsPhysicalStrong` from hypotheses 1–4.

## P8_PhysicalGap Campaign History (C87–C102)

| Campaign | Tag | Key Elimination |
|----------|-----|----------------|
| C87 | v1.03.0 | OperatorNormBound: exp decay from op-norm + SpectralGap |
| C88 | v1.04.0 | SpectralGap from ‖T(1-P₀)‖ ≤ e^{-m} norm bound |
| C89–C96 | v1.05–v1.12 | Eliminated: selfAdj, rank-one P₀, TΩ=Ω, ‖Ω‖=1, Ω existence, exp(-m) bound |
| C97–C100 | v1.13–v1.16 | Eliminated: isometry, continuity, Lipschitz→StateNorm, FK witness |
| C101 | v1.17.0 | Reduced FK to transfer-matrix assumptions |
| C102 | v1.18.0 | **Cauchy-Schwarz bridge**: FK+StateNorm → FeynmanKacOpNormBound |

## Oracle Policy

Every P8_PhysicalGap theorem must pass:
```bash
#print axioms YangMills.<theorem>
-- Required: [propext, Classical.choice, Quot.sound]
-- Forbidden: sorry, yangMills_continuum_mass_gap, any new axiom
```

## Multi-Agent Deployment Loop

```
strategist → executor → build/oracle/push → librarian (docs) → architect → next campaign
```

Campaigns deployed via `deploy_CXX.py` scripts in Google Colab.

## Repository

- **GitHub**: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME
- **Colab**: https://colab.research.google.com/drive/1LAkT6uhn-czP2EbO5qQhcYUtqFSZQUXs
- **Author**: Lluís Eriksson
