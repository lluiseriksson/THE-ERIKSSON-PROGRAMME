# The Eriksson Programme

**Formalizing the Clay Millennium Yang–Mills mass gap theorem in Lean 4.**

Active development. No `sorry`, no project-specific axioms. Oracle fixed at `[propext, Classical.choice, Quot.sound]`.

---

## What this is

A Lean 4 + Mathlib project formalizing the mass gap for pure-gauge SU(N) lattice Yang–Mills theory via the character-expansion / cluster-decay strategy. The proof is split into three independent layers so that each can be attacked, verified, and extended in isolation:

1. **Haar machinery + Schur orthogonality on SU(N)** — proved directly from Mathlib's `Matrix.specialUnitaryGroup` and `MeasureTheory`.
2. **Character expansion / cluster decay correlator bound** — currently encapsulated as an abstract `CharacterExpansionData` structure; the cluster bound itself is the nontrivial physical content and the main conditional hypothesis.
3. **Mass-gap conclusion from the correlator bound** — a transfer-matrix / OS-reconstruction calculation that derives the gap once (2) is supplied.

---

## Status (2026-04-21, v0.34.x)

| Layer | Progress | Oracle clean |
|---|---|---|
| L1 — Haar measure on SU(N) (`sunHaarProb`) | complete | yes |
| L2.1–L2.4 — compactness, measurability, trace / Frobenius | complete | yes |
| L2.5 — `integral of ‖tr U‖² ≤ N` | complete (v0.34.0) | yes |
| L2.6 — Schur entry orthogonality | in progress — step 1b-i of ~4 | yes so far |
| L3.1 / L3.2 — Cluster decay bound | assumed as `h_correlator` | N/A |
| L4.1 — Mass gap conclusion | scaffolded, conditional | yes |
| Final wiring | not done | — |

### L2.6 sub-plan

- step 0 `SchurDiagPhase.lean` — diagonal phase `diag(exp(I·θ_k))` in SU(N), oracle clean.
- step 1a `SchurEntryOrthogonality.lean` — antisymmetric angle `antiSymAngle i k`.
- **step 1b-i** (current) — π-scaled phase, `exp(I·(θ_i − θ_k)) = exp(I·π) = −1`.
- step 1b-ii — off-diagonal integral vanishing via left-invariance against `piAntiSymSU`.
- step 2 — diagonal case and the `1/N` normalization constant.
- step 3 — orthogonality for irreducible character matrix elements.

---

## Honest conditionality assessment

| Definition of "100%" | Current progress |
|---|---|
| Full Clay-quality (any coupling, continuum) | ~3% |
| Strong-coupling Wilson action, rigorous gap | ~20% |
| Modular chain with `h_correlator` as only remaining assumption | ~65% |
| Modular chain with abstract `CharacterExpansionData` as input | ~75% |

The jump from "conditional" to "unconditional strong-coupling" requires proving the cluster decay estimate at large β — tractable but significant (6–12 months at current pace). The jump to unconditional Clay-quality is an open mathematical problem.

---

## Structure

    YangMills/
      ClayCore/
        SchurL25.lean                 -- L2.5: trace norm^2 bound
        SchurDiagPhase.lean           -- L2.6 step 0
        SchurTwoSitePhase.lean        -- two-site (I, -I, 1, ...) phase
        SchurOffDiagonal.lean         -- off-diagonal Frobenius term
        SchurEntryOrthogonality.lean  -- L2.6 steps 1a + 1b-i
        CharacterExpansion.lean       -- CharacterExpansionData + gap theorem
        SchurPhysicalBridge.lean      -- physical observable interface
        CLAY_CORE_STATUS.md           -- deep-dive status on the core layer
        NEXT_SESSION.md               -- plan for the next work session
      P8_PhysicalGap/
        SUN_Compact.lean              -- topology and measurability

---

## Build

Full build:

    lake build

Single module:

    lake build YangMills.ClayCore.SchurEntryOrthogonality

Oracle check — verify a declaration depends only on Lean's core three axioms. In a scratch `.lean` file:

    import YangMills.ClayCore.SchurEntryOrthogonality
    #print axioms YangMills.ClayCore.piAntiSymSU_phase

Expected: `depends on axioms: [propext, Classical.choice, Quot.sound]`.

---

## Working rules

- No `sorry`.
- No project-specific axioms.
- Oracle stays `[propext, Classical.choice, Quot.sound]` for all core declarations.
- Every commit green under `lake build`.
- Oracle-checked before every commit.
- Docs (`README.md`, `STATE_OF_THE_PROJECT.md`, `AXIOM_FRONTIER.md`) updated every ~3 commits.
- Files split at ~150 lines.

---

## Related files

- `STATE_OF_THE_PROJECT.md` — detailed version-by-version progress.
- `AXIOM_FRONTIER.md` — evolving list of closed/open conditional axioms.
- `YangMills/ClayCore/CLAY_CORE_STATUS.md` — deep-dive status on the core layer.
- `YangMills/ClayCore/NEXT_SESSION.md` — plan for the next session.

---

Lluis Eriksson — The Eriksson Programme.