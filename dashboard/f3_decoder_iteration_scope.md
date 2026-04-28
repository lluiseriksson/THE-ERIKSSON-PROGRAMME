# F3-COUNT §(b)/B.2 — Word Decoder Iteration Scope

**Cowork-authored Codex-ready signature scaffold for the §(b)/B.2 word decoder iteration.**

**Author**: Cowork
**Created**: 2026-04-26T22:10:00Z (under `COWORK-F3-DECODER-ITERATION-SCOPE-001`)
**Status**: **forward-looking blueprint only**. §(b)/B.2 is **not proved**; this document is a Codex-ready scope, not a proof. F3-COUNT remains `CONDITIONAL_BRIDGE`.

---

## Mandatory disclaimer

> §(b)/B.2 word decoder iteration is **OPEN**. F3-COUNT closure requires
> BOTH B.1 (`PlaquetteGraphAnchoredHighCardTwoNonCutExists` for `4 ≤ k`,
> post-v2.60) AND B.2 (this iteration). This document scopes B.2 only. After
> Codex closes B.1, the actual implementation work in §(b)/B.2 begins;
> this scope just pre-supplies the signature so Codex doesn't have to rediscover
> the API surface from scratch. **Nothing in this document moves the F3-COUNT
> row from `CONDITIONAL_BRIDGE`.**

---

## Context

`F3_COUNT_DEPENDENCY_MAP.md` §(d) (lines 431+) gives a high-level pseudocode
for the iterated decoder, but the detailed Lean signature scaffold is missing.
Once Codex closes the v2.60 high-card target
`PlaquetteGraphAnchoredHighCardTwoNonCutExists` for `4 ≤ k`, the `k = k-1`
recursive step is unblocked and §(b)/B.2 becomes the last math step before
F3-COUNT closure. Cowork pre-supplies the scope below.

The §(b)/B.2 target is to discharge `PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296`
unconditionally. The line-1096 consumer
(`physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296`)
then fires automatically and produces the full Klarner exponential bound
`count(n) ≤ 7^n` (via the `1296 = 6^4` four-dimensional alphabet).

---

## (a) Precise Lean signature

The target theorem to be proved unconditionally in §(b)/B.2:

```lean
theorem PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved
    (hsafe : PlaquetteGraphAnchoredSafeDeletionExists physicalClayDimension)
    -- closed by v2.60 + B.1 (PlaquetteGraphAnchoredHighCardTwoNonCutExists for 4 ≤ k)
    -- via plaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists
    -- (LatticeAnimalCount.lean:2359) composed with v2.59 base-zone driver
    : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
```

Or, eliminating the hypothesis once B.1 is fully proved:

```lean
theorem PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved
    : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
```

**Unfolded statement** (per `LatticeAnimalCount.lean:1057-1064` + `:1084-1085`):

```lean
∀ {L : ℕ} [NeZero L]
  (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ),
  ∃ baseline : Finset (ConcretePlaquette physicalClayDimension L),
  ∃ decodeExtra : (Fin n → Fin 1296) →
      Finset (ConcretePlaquette physicalClayDimension L),
    ∀ X : ConnectingClusterBucket physicalClayDimension L p q n,
      ∃ word : Fin n → Fin 1296, baseline ∪ decodeExtra word = X.1
```

So the proof must:
1. Choose a baseline `Finset` (Cowork recommendation: `{p, q}` plus a deterministic
   shortest-path baseline between `p` and `q`).
2. Construct a function `decodeExtra : (Fin n → Fin 1296) → Finset (...)` — the
   word-to-bucket decoder.
3. Show that for every bucket `X : ConnectingClusterBucket physicalClayDimension L p q n`,
   some word `word : Fin n → Fin 1296` decodes to `X.1` modulo baseline.

---

## (b) Structural-induction skeleton

The natural induction is on `k = X.card - baseline.card` (the remaining
plaquettes beyond the baseline). Without loss of generality, view the bucket
member `X` as an anchored bucket with root `p` (or root `q`, then concatenate).

### Base cases

```lean
-- k = 0: trivial (X = baseline).
| 0 => fun _ => ⟨fun _ => ∅, fun _ => rfl⟩

-- k = 1: single-root bucket; word is empty (Fin 0 → Fin 1296),
--        decoded to {root} via plaquetteGraphPreconnectedSubsetsAnchoredCard_singleton.
| 1 => fun _ => ⟨..., ...⟩
```

### Inductive step (`k+1 → k`)

The recursive call uses the **safe-deletion driver** (closed by v2.60 + B.1):

```lean
| k+1 => by
  -- Step 1: Pick a non-root deleteable plaquette via the safe-deletion driver.
  obtain ⟨z, hzX, hz_ne_root, hz_in_smaller⟩ :=
    hsafe (root := root) (k := k+1) (X := X)
      (by omega : 1 < k + 1) hX
  -- (hz_in_smaller : X.erase z ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard ... root k)

  -- Step 2: Encode `z`'s parent path via v2.48 rootShellParentCode1296.
  let parentSymbol : Fin 1296 :=
    physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296
      hX_smaller ⟨z, hzX, hz_ne_root.symm⟩

  -- Step 3: Recurse on X.erase z (which has cardinality k).
  obtain ⟨word_smaller, hword_smaller⟩ :=
    iterationStep (X := X.erase z) hz_in_smaller k

  -- Step 4: Concatenate parentSymbol :: word_smaller, return.
  refine ⟨Fin.cons parentSymbol word_smaller, ?_⟩
  -- Show baseline ∪ decodeExtra (Fin.cons parentSymbol word_smaller) = X.1
  rw [decodeExtra_cons]; ...
```

The recursive call is on `X.erase z`, whose membership in the smaller bucket
family is supplied by the safe-deletion driver itself (via
`plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected` at
`LatticeAnimalCount.lean:1666`).

---

## (c) Encoding contract

Each iteration step writes **one `Fin 1296` symbol**. The `1296`-letter
alphabet is the 4-dimensional plaquette neighbor alphabet
(`6^4 = 1296` possible ±-direction × ±-orientation choices for a plaquette
neighbor).

Symbol per step is given by **v2.48 `rootShellParentCode1296`** at:

```
LatticeAnimalCount.lean:2629
noncomputable def physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296
    {L k : ℕ} [NeZero L]
    {root : ConcretePlaquette physicalClayDimension L}
    {X : Finset (ConcretePlaquette physicalClayDimension L)}
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k)
    (y : {y : ConcretePlaquette physicalClayDimension L // y ∈ X ∧ root ≠ y}) :
    Fin 1296
```

The companion theorem **`..._spec`** at `LatticeAnimalCount.lean:2681` is the
**code-stability equation** required when iterating the parent map:

```lean
physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296 hX
  (physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296 hX y) =
  physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296 hX y
```

i.e. the symbol the parent emits at level `k` is the same symbol that level
`k-1` would re-emit if asked — this is what makes the word stable across
iteration boundaries. Without `..._spec`, an aggressive recursive step could
not pass through a fresh `Classical.choose` each level.

---

## (d) Termination argument

The recursion terminates after **exactly `n` steps** (or `X.card - baseline.card`
steps, whichever frame the caller uses). The strict-decrease witness at each
step is **v2.50 `firstDeleteResidual1296_card`** at:

```
LatticeAnimalCount.lean:1618
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296_card
    ... (hk : 1 < k) :
    (...firstDeleteResidual1296 hX hk).card = k - 1
```

This is a **direct cardinality-decreases** lemma, not a well-founded-recursion
hack. The Lean `termination_by` clause should read:

```lean
termination_by _ X _ => X.card
```

With the recursive call passing `X.erase z`, whose cardinality is `X.card - 1`
by `Finset.card_erase_of_mem` (since `z ∈ X` is supplied by the safe-deletion
driver).

The base cases `k = 0` and `k = 1` are reached after exactly `X.card`
recursive descents, matching the word length `n = X.card - baseline.card`.

**Companion lemma needed** (likely already provable from existing API):

```lean
theorem physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteResidual1296_root_mem
    -- already exists at LatticeAnimalCount.lean:1637
```

confirms the root remains in the residual after one peel. Combined with v2.50
`_card` and the v2.60 + B.1 safe-deletion existential, the recursion is
**terminating, root-preserving, and cardinality-strictly-decreasing**.

---

## (e) Connection to Klarner bound `count(n) ≤ 7^n`

Once `PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved` is
proved, the **line-1096 consumer**

```
LatticeAnimalCount.lean:1096
def physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296) :
    -- produces PhysicalShiftedConnectingClusterCountBoundExp 1 1296
```

fires automatically (it is already proved at `:1089-1092`). The composition
chain to Klarner is:

```
PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved   (B.2 — this scope)
  → PhysicalConnectingClusterExtraWordDecoderBound 1296              (line 1068)
  → PhysicalShiftedConnectingClusterCountBoundExp 1 1296             (line 1042)
  → PhysicalShiftedConnectingClusterCountBoundExp 1 1296             (line 1089, abbrev to 1296)
  → ShiftedConnectingClusterCountBoundExp 1 1296                     (consumer at line 1096)
  → count(n) ≤ 1296^n = 6^(4n) ≤ 7^(4n)                              (Klarner bound, base 7^d for d=4)
```

The `1296^n` bound is what Klarner-style F3-COUNT delivers in 4 dimensions
with the 6×4-direction alphabet. The downstream OS / mass-gap chain consumes
`count(n) ≤ K^n` for any fixed `K` of the right order — `1296^n` works
because the lattice `K = 7` Klarner constant for d=4 satisfies `7^4 = 2401 > 1296`,
i.e. the alphabet-2 baseline is tighter than the project's headline `K = 7`.

When this composition fires:
- **F3-COUNT** moves from `CONDITIONAL_BRIDGE` → `FORMAL_KERNEL`.
- **F3-MAYER** unblocks (was `BLOCKED on F3-COUNT closure first`).
- **F3-COMBINED** can begin (was `BLOCKED on F3-COUNT and F3-MAYER`).
- Lattice 28% → ~43% (per `F3_COUNT_DEPENDENCY_MAP.md` §(e) line 309).

---

## Summary table — pre-supplied API surface for §(b)/B.2

| Section | Lean object | File:line | Role in §(b)/B.2 |
|---|---|---|---|
| (a) signature | `PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296` | `:1084-1085` | The unconditional target |
| (a) signature | `PhysicalConnectingClusterBaselineExtraWordDecoderCovers` (general K) | `:1057-1064` | Unfolded-K version |
| (b) skeleton | `plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected` | `:1666-1684` | The k+1 → k recursive handoff (consumes safe-deletion) |
| (b) safe-deletion input | `PlaquetteGraphAnchoredSafeDeletionExists` | (closed by v2.60 + B.1) | The hypothesis the iteration consumes |
| (b) bridge to safe-deletion | `plaquetteGraphAnchoredSafeDeletionExists_of_highCardTwoNonCutExists` | `:2359` | Connects v2.60 high-card to the iteration |
| (c) encoding | `..._rootShellParentCode1296` | `:2629-2639` | Symbol per step (Fin 1296) |
| (c) encoding | `..._rootShellParentCode1296_spec` | `:2681-2696` | Code-stability equation across iteration |
| (d) termination | `..._firstDeleteResidual1296_card` | `:1618-1633` | k → k-1 strict-decrease witness |
| (d) termination | `..._firstDeleteResidual1296_root_mem` | `:1637-1658` | Root-preserved-after-peel |
| (e) consumer | `physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296` | `:1096` | Fires once B.2 lands |
| (e) consumer | `physicalConnectingClusterExtraWordDecoderBound_of_baselineExtraWordDecoderCovers` | `:1068-1073` | Word-decoder lift |
| (e) consumer | `physicalShiftedConnectingClusterCountBoundExp_of_extraWordDecoder` | `:1042-1052` | Decoder-to-count bridge |

---

## What this scope does NOT do

- **Does not prove** `PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296`.
- **Does not move** F3-COUNT from `CONDITIONAL_BRIDGE`.
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** B.1 (the v2.60 high-card target) is closed; it scopes
  B.2 conditional on B.1 + v2.59 base-zone composition.

When Codex closes B.1, this scope tells Codex exactly which existing API
elements to compose. Estimated B.2 implementation: ~150-250 LOC of pure
mechanical iteration — no new mathematical content beyond what B.1 already
delivers, just careful structural-induction bookkeeping.

---

## Honesty preservation

- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`)
- F3-MAYER row: still `BLOCKED`
- F3-COMBINED row: still `BLOCKED`
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%
- This document is a **forward-looking blueprint**, not a proof artifact.

---

## Cross-references

- `F3_COUNT_DEPENDENCY_MAP.md` §(d) lines 431-490 — high-level pseudocode for the iteration
- `F3_COUNT_DEPENDENCY_MAP.md` §(b)/B.2 lines 303+ — the original §(b)/B.2 sketch
- `BLUEPRINT_F3Count.md` — Klarner BFS-tree sketch (parent-of-this-document)
- `AXIOM_FRONTIER.md` v2.60.0 lines 67-77 — confirms the high-card structural reduction
- `UNCONDITIONALITY_LEDGER.md:97` — F3-COUNT row (`CONDITIONAL_BRIDGE`)
