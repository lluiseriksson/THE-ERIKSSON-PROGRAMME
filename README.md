# THE ERIKSSON PROGRAMME

**A Lean 4 / Mathlib formalization of the Yang–Mills mass gap, organized around an oracle-clean core and an explicit path to 100 % unconditionality.**

- Lean toolchain: `leanprover/lean4:v4.29.0-rc6`
- Mathlib: pinned to `master` (see `lakefile.lean`)
- License: see `LICENSE`
- Current front: **L2.6 step 1c — the diagonal Schur integral `∫_{SU(N)} |U_ij|² dμ = 1/N`**
- Last core milestone closed: **L2.6 step 1b — off-diagonal Schur orthogonality on matrix entries** (commit `0143c37`)

---

## 1. What this repository is

The repository formalizes, in Lean 4 + Mathlib, the chain of analytic and representation-theoretic facts used in a Yang–Mills mass-gap argument. The long-term target is the Clay Millennium Prize problem: proving the existence of a quantum Yang–Mills theory on ℝ⁴ with a positive mass gap.

The formal content is split into three layers:

- **L1 — Haar + Schur on `SU(N)`.** The base layer. Haar probability measure, left/right invariance, and Schur orthogonality for matrix coefficients of unitary irreducible representations. This is the layer where the current front (L2.6 step 1c) lives.
- **L2 — Character expansion and cluster decay.** Wilson-loop expansions, polymer / Mayer expansions, exponential cluster bounds. Builds on L1 but is structurally separable.
- **L3 — Mass-gap conclusion.** The final logical step: from L1+L2 (plus conditional physical hypotheses collected as `CharacterExpansionData` and `h_correlator`) to a two-point-function bound giving a mass gap.

The conditional structure is intentional. Every physics hypothesis that is *not* fully Lean-checked yet is surfaced as a named `structure` field or a named `axiom`, and lives in `AXIOM_FRONTIER.md`. L3's final statement takes those as hypotheses; the goal of the unconditionality roadmap is to discharge them one by one inside L1–L2.

---

## 2. Status — 2026-04-22

| Milestone | Statement | Status |
| --- | --- | --- |
| L2.4 | Structural Schur / Haar scaffolding on `SU(N)` | DONE |
| L2.5 | `∑_i ∫_{SU(N)} |U_ii|² dμ ≤ N`  (Frobenius trace bound) | DONE |
| L2.6 step 0 | Diagonal phase element of `SU(N)` (pure-phase block) | DONE |
| L2.6 step 1a | Antisymmetric two-site angle + `antiSymSU` scaffold | DONE |
| L2.6 step 1b-i | π-scaled antisymmetric phase, `exp(I·π) = −1` | DONE |
| L2.6 step 1b-ii | Off-diagonal entry Haar integral vanishes for `i ≠ k` | DONE |
| L2.6 step 1b (column + general) | Off-diagonal Schur orthogonality, matrix-entry form | DONE |
| **L2.6 step 1c** | **Diagonal Schur integral `∫ |U_ij|² dμ = 1/N`** | **IN PROGRESS** |
| L2.6 step 2 | Full diagonal orthogonality + normalization constant `1/N` | QUEUED |
| L2.6 step 3 | Irreducible-character orthogonality on `SU(N)` | QUEUED |

The L2.6 step 1c target file is `YangMills/ClayCore/SchurEntryDiagonal.lean` (currently a scaffold).

For the full picture, see:

- `STATE_OF_THE_PROJECT.md` — global snapshot
- `UNCONDITIONALITY_ROADMAP.md` — ordered plan to 100 % unconditional
- `AXIOM_FRONTIER.md` — every remaining conditional axiom, with its physical meaning
- `PETER_WEYL_ROADMAP.md` — Peter–Weyl / character-theory path beyond L2.6
- `SORRY_FRONTIER.md` — every remaining `sorry`, with the module and line

---

## 3. Oracle discipline (scope of the "no sorry" claim)

The `YangMills/ClayCore/` subtree — the L1 + central L2 chain through Schur orthogonality and the trace/Frobenius bound — is held to a strict oracle budget:

    #print axioms <theorem>  ⟹  [propext, Classical.choice, Quot.sound]

No project-specific `axiom`, no `sorry`, nothing beyond Lean's three foundational oracles. Any commit that enlarges the axiom print of a ClayCore theorem is rejected.

**This discipline is scoped to `YangMills/ClayCore/` only.** Peripheral modules that model Balaban RG, Dirichlet / Bakry–Émery, Lie-derivative regularity, and Stroock–Zegarliński-type LSI inputs still carry conditional `axiom` declarations and a small number of `sorry`s. These are the declared physics hypotheses of L3, each tracked individually in `AXIOM_FRONTIER.md` and `SORRY_FRONTIER.md`. The unconditionality roadmap is precisely the plan to eliminate those peripheral entries one at a time, starting from the L1 end.

So: the *core* is oracle-clean today. The *whole project* is not — and we say so out in the open, file by file.

---

## 4. Path to 100 % unconditional — L2.6 step 1c

**Target statement.** For `N ≥ 1` and any matrix entry `(i, j)` of a Haar-distributed `U ∈ SU(N)`,

    ∫_{SU(N)} U_ij · star(U_ij) dμ_Haar = 1 / N

i.e. every entry has squared Haar-norm exactly `1/N`. Together with L2.6 step 1b (off-diagonals vanish) this closes matrix-entry Schur orthogonality on `SU(N)`.

### 4.1 Why this is the right next brick

- **Downstream.** Character orthogonality on `SU(N)` (L2.6 step 3) factors cleanly through entry orthogonality plus the Peter–Weyl decomposition. Without the diagonal `1/N` normalization, every L2 cluster-expansion bound carries an unknown multiplicative constant.
- **Upstream.** L2.5 already proves `∑_i ∫ |U_ii|² dμ ≤ N` on `SU(N)`. Combined with symmetry across diagonal entries (via a row/column swap in `SU(N)`), this upper bound becomes an *equality* and splits into `1/N` per entry. Step 1c is the place where "≤ N" becomes "= N" becomes "= 1/N each".

### 4.2 Proof strategy in Lean

The file `YangMills/ClayCore/SchurEntryDiagonal.lean` will carry three lemmas, in this order:

1. **`rotPairMat_mem_SU` — a quarter-rotation is special unitary.** For `i ≠ j` define `rotPairMat i j : Matrix (Fin N) (Fin N) ℂ` as the identity everywhere except on the 2×2 block `(i,j)` where it is the real rotation `[[0,−1],[1,0]]`. This matrix is unitary, has determinant `1` (the block has det `1`), and is therefore in `SU(N)`. This is a mechanical check on top of the `rotPairMat` skeleton that already lives in `SchurTwoSitePhase.lean`.

2. **`entry_sq_invariant_under_index_swap`.** For `R := rotPairMat i j`, the map `U ↦ R · U · R⁻¹` is a measure-preserving bijection of `SU(N)` under Haar (by `IsMulLeftInvariant` and `IsMulRightInvariant` of `MeasureTheory.Measure.haar` on the compact group `SU(N)`). Under conjugation by `R`, entry `(i,i)` of `U` is sent to entry `(j,j)` of the conjugated matrix, up to a sign that squares to `1`. Taking `|·|²` and integrating:

        ∫ |U_ii|² dμ  =  ∫ |U_jj|² dμ       for all i, j.

   This is the symmetrization step. It is the one place the argument actually uses the structure of `SU(N)` beyond `U(N)` — we need to know that `rotPairMat i j` is in the subgroup, which is exactly step 1 above.

3. **`sunHaarProb_entry_normSq_eq_inv_N`.** Combine with L2.5:

        N · (∫ |U_11|² dμ)  =  ∑_i ∫ |U_ii|² dμ  =  ∫ ∑_i |U_ii|² dμ  =  ∫ ‖row_1 U‖² dμ  =  1

   (the last equality because every row of a unitary has unit Euclidean norm, pointwise; the Frobenius normalization already proved in L2.5 collapses from `≤ N` to `= N` on the full sum because rows of `U` are unit vectors *pointwise*, not merely on average). Divide by `N` to get `∫ |U_11|² dμ = 1/N`, and apply step 2 to move the index.

### 4.3 Oracle budget

Every lemma in `SchurEntryDiagonal.lean` is required to type-check against

    #print axioms
      ⟶ [propext, Classical.choice, Quot.sound]

only. The three ingredients used — `SU(N)` group structure (Mathlib), Haar left/right invariance on a compact group (Mathlib), and L2.5's pointwise row-norm identity (already in `SchurL25.lean`) — all pass the oracle check today. Step 1c therefore lands the diagonal Schur integral inside the oracle-clean core.

### 4.4 What step 1c does *not* do

Step 1c does not prove full character orthogonality (`∫ χ_λ · conj χ_μ dμ = δ_{λμ}`) — that is L2.6 step 3, and it goes through Peter–Weyl. It also does not touch any L3 physics hypothesis. Its sole deliverable is the matrix-entry identity `∫ |U_ij|² dμ = 1/N` and the immediate corollary `∫ U_ij · conj U_kl dμ = δ_{ik} δ_{jl} / N` obtained by combining with step 1b.

---

## 5. Repository layout

    YangMills/
      ClayCore/                    ← oracle-clean core (L1 + central L2)
        SchurDiagPhase.lean        ← L2.6 step 0
        SchurTwoSitePhase.lean     ← L2.6 step 1a / 1b
        SchurOffDiagonal.lean
        SchurEntryOffDiag.lean     ← L2.6 step 1b (columns, general)
        SchurEntryOrthogonality.lean
        SchurEntryDiagonal.lean    ← L2.6 step 1c (current front)
        SchurL25.lean              ← L2.5 closed
        SchurNormSquared.lean
        SchurZeroMean.lean
        SchurPhysicalBridge.lean
        CharacterExpansion.lean
        …                          ← Wilson / Cluster / Balaban / Mayer machinery
      (peripheral L3 modules: Balaban, Dirichlet, LieDeriv, Hille–Yosida,
       Bakry–Émery, Stroock–Zegarliński — carry declared axioms + a small
       number of sorries tracked in AXIOM_FRONTIER.md and SORRY_FRONTIER.md)
    docs/
    papers/
    registry/
    scripts/
    dashboard/
    README.md                      ← this file
    AXIOM_FRONTIER.md
    SORRY_FRONTIER.md
    UNCONDITIONALITY_ROADMAP.md
    PETER_WEYL_ROADMAP.md
    STATE_OF_THE_PROJECT.md
    ROADMAP.md / ROADMAP_MASTER.md
    HYPOTHESIS_FRONTIER.md
    DECISIONS.md
    CONTRIBUTING.md
    AI_ONBOARDING.md

---

## 6. Building

    lake update
    lake build YangMills.ClayCore

To verify the oracle budget of a specific theorem:

    -- at the end of any ClayCore file
    #print axioms your_theorem_name
    -- expected: [propext, Classical.choice, Quot.sound]

CI refuses a ClayCore commit that prints any other axiom name.

---

## 7. How to contribute

1. Read `AI_ONBOARDING.md` and `CONTRIBUTING.md`.
2. Pick an entry from `AXIOM_FRONTIER.md` or the current front (`SchurEntryDiagonal.lean`).
3. Keep `YangMills/ClayCore/` oracle-clean; land physics hypotheses in peripheral modules with a *named* `axiom` declaration and a matching row in `AXIOM_FRONTIER.md`.
4. Open a PR with a `#print axioms` trace for every theorem added to ClayCore.

---

## 8. Honesty note

This project will not be considered a full proof of the Clay Yang–Mills mass gap until `AXIOM_FRONTIER.md` is empty and `SORRY_FRONTIER.md` is empty at the same commit, and L3's top theorem `#print axioms`-prints only `[propext, Classical.choice, Quot.sound]`. We are not there yet. L2.6 step 1c is one rung on that ladder — a concrete, oracle-clean one. Every milestone en this README is stated with its exact status and a pointer to the file where it lives, so that any reader can check the gap between claim and proof themselves.
