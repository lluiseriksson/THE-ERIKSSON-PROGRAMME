# PETER_WEYL_AUDIT.md

**Author**: Cowork agent (Claude), audit pass 2026-04-25
**Subject**: post-reclassification verification of `PETER_WEYL_ROADMAP.md`
**Period covered**: from 2026-04-22 evening reclassification through 2026-04-25
**Method**: consumer-driven dependency tracing of all post-reclassification commits

---

## 0. Bottom line

The 2026-04-22 evening reclassification of Peter–Weyl as "aspirational /
Mathlib-PR — not Clay critical path" **holds in full**. No new commits
since the reclassification have re-introduced Peter–Weyl content as a
Clay dependency. The roadmap's Section 5 "Recommended ordering for next
5 Colab sessions" is **partially executed in spirit**:

- "Path A (U(1) abelian warmup)" — **executed**. `AbelianU1Unconditional.lean`
  (commit 2026-04-23) produces `u1_clay_yangMills_mass_gap_unconditional :
  ClayYangMillsMassGap 1`, the first concrete Clay-statement inhabitant,
  bypassing Peter–Weyl entirely via `Subsingleton (Matrix.specialUnitaryGroup
  (Fin 1) ℂ)`.
- "First milestone — `sunHaarProb_trace_re_integral_zero`" — **superseded**.
  The team did not pursue the bare degree-1 statement; instead they closed
  the whole L2.6 main target (`sunHaarProb_trace_normSq_integral_eq_one`,
  commit f9ec5e9) which is the L1→L2 interface that L2's cluster expansion
  actually consumes. The degree-1 vanishing was implicit en route.
- "Sessions N+2 to N+5" — **abandoned in favour of F3 frontier**. The team
  pivoted to the F3-Mayer / F3-Count frontier as documented in
  `BLUEPRINT_F3Count.md` and `BLUEPRINT_F3Mayer.md`. The Peter–Weyl roadmap
  remains aspirational / Mathlib-PR.

The roadmap document itself (574 lines) is now ~80% **stale** —
specifically Sections 1, 2, 3 (Layers 0–4 architecture), 4 (first
milestone), 5 (recommended ordering). The reclassification banner at the
top is accurate. The references in Section 7 remain useful.

**Recommendation**: do not delete the document, but **trim it** to keep
only the reclassification record + Layer-4 / Layer-5 sketches that fed
into the F3 design. See §5 below for proposed trim.

---

## 1. Method

I enumerated all files added or substantially modified in
`YangMills/ClayCore/` and `YangMills/L8_Terminal/` since the 2026-04-22
18:00 reclassification, and traced each one along two axes:

(a) **Does it introduce Peter–Weyl-vocabulary content?** (Search keys:
    `Peter`, `Weyl`, `character`, `irrep`, `matCoeff`, `orthonormal`,
    `peterWeyl`, `matrix.coeff`, `Representation.character`.)

(b) **Does it ultimately flow to one of the Clay endpoints
    `ClayYangMillsMassGap`, `ClayConnectedCorrDecay`, or the vacuous
    triplet (`ClayYangMillsTheorem`, `ClayYangMillsStrong`,
    `ClayYangMillsPhysicalStrong`)?**

A file is **load-bearing** if it both (b)-flows AND its specific
contribution is **necessary** for the flow (i.e. removing it breaks the
chain). It is **vestigial** if (a)-keyword AND not (b)-load-bearing.

---

## 2. Files added since reclassification — verdict

| File | Lines | (a)-keyword? | (b)-load-bearing? | Verdict |
|---|---:|---|---|---|
| `AbelianU1Unconditional.lean` | 226 | no | yes (U(1) Clay witness) | **load-bearing** |
| `ClusterRpowBridge.lean` | 4264 | no | yes (F3 chain hub) | **load-bearing** |
| `ConnectedCorrDecay.lean` | 190 | no | yes (`ClayConnectedCorrDecay` structure consumer) | **load-bearing** |
| `ConnectingClusterCountExp.lean` | 14822 b | no | yes (F3-Count exp frontier — see `BLUEPRINT_F3Count.md`) | **load-bearing** |
| `LargeFieldDominance.lean` | ? | no | yes (Balaban P2a, downstream of asymptotic-freedom path) | **load-bearing** |
| `SchurTracePow.lean` | ? | "Schur" only — scalar trace subalgebra | yes (L2.6 sidecar 3a) | **load-bearing (sidecar)** |
| `SchurTracePowBilinear.lean` | ? | "Schur" only — scalar trace subalgebra | yes (L2.6 sidecar 3b) | **load-bearing (sidecar)** |
| `SchurTraceUPow.lean` | ? | "Schur" only — scalar trace subalgebra | yes (L2.6 sidecar 3c) | **load-bearing (sidecar)** |
| `L8_Terminal/ClayTrivialityAudit.lean` | ? | no | meta — records that `ClayYangMillsTheorem` is logically `True` | **load-bearing (audit)** |

**Zero new files re-introduce Peter–Weyl content.** The "Schur" prefix
on the three sidecar files refers to **Schur orthogonality on the scalar
trace subalgebra**, which (per the reclassification) is the only fragment
of Peter–Weyl actually needed for L2.6. These are the Layer-2.6 sidecars
{3a, 3b, 3c} the README acknowledges as closed.

**Conclusion of (a)-axis**: the team has not regressed. No deadweight
re-introduction.

---

## 3. (b)-axis: which Clay endpoints currently have witnesses?

| Endpoint | Witness? | Source | Notes |
|---|---|---|---|
| `ClayYangMillsTheorem` | yes (vacuous) | various | logically `True`, audited in `ClayTrivialityAudit.lean` |
| `ClayYangMillsStrong` | yes (vacuous via `constantMassProfile 1`) | `ClayPhysical.lean` | also weak |
| `ClayYangMillsPhysicalStrong` | partial | depends on observable | non-vacuous claim, requires non-degenerate F |
| `ClayYangMillsMassGap 1` | **yes (unconditional)** | `AbelianU1Unconditional.lean` | first authentic non-vacuous witness; uses `Subsingleton` of SU(1) |
| `ClayYangMillsMassGap N_c` (for N_c ≥ 2) | **no — open** | F3-Mayer + F3-Count needed | the **real** target; both blueprints address this |
| `ClayConnectedCorrDecay N_c` | partial | `ClusterRpowBridge.lean` | several constructors via F3 chain, all gated on the open packages |

The diagonal of the file is: **N_c = 1 is closed unconditionally; N_c ≥ 2
is gated entirely on the two F3 packages**. Peter–Weyl provides no
shortcut to either; the F3 path bypasses it via the scalar-trace
subalgebra (sidecars 3a/3b/3c) plus the L2.6 main target.

---

## 4. Stale claims in `PETER_WEYL_ROADMAP.md`

The following sections are **stale** as of 2026-04-25:

- **Section 1 (Target statement)**: still describes
  `ConnectedCorrDecay` from `P3_BalabanRG/CorrelationNorms.lean` as the
  bottleneck. The bottleneck has shifted to
  `PhysicalShiftedF3MayerPackage` / `PhysicalShiftedF3CountPackage` per
  `NEXT_SESSION.md` and `BLUEPRINT_F3*.md`. **Not deleted** because
  `ConnectedCorrDecay` is still a valid downstream consumer.
- **Section 2 (Mathlib availability)**: enumerates AVAILABLE / PARTIAL /
  MISSING for Peter–Weyl machinery. Accurate but **superseded** by
  `MATHLIB_GAPS.md` (in production by Cowork agent next).
- **Section 3 (Layers 0–5)**: this is the bulk of the document (~250
  lines) and describes a path that is no longer being pursued. Since
  Layer 4's `wilson_polymer_activity_bound` and Layer 5's assembly
  **directly inspired** the F3-Mayer construction (BK estimate +
  small-β + cluster decay), this content has lasting value as a design
  reference. **Recommend trimming Layers 0–3 to one-paragraph
  summaries; preserve Layer 4 + 5 with a header noting the
  redirection to the F3 frontier**.
- **Section 4 (First milestone)**: superseded. The team did not pursue
  this milestone in isolation; the L2.6 main target subsumed it.
  **Recommend deletion** (or one-line "subsumed by L2.6 main target,
  commit f9ec5e9").
- **Section 5 (Critical path / 5-session ordering)**: superseded by
  the F3 frontier. **Recommend deletion**.
- **Section 6 (What this roadmap does not promise)**: still accurate
  and worth keeping verbatim — particularly the continuum-limit
  caveat (`HasContinuumMassGap`) which is still outside scope.
- **Section 7 (References)**: keep.

---

## 5. Proposed trim

A trimmed `PETER_WEYL_ROADMAP.md` of ~150 lines (down from 574) would
keep:

1. The 2026-04-22 reclassification banner (verbatim, ~25 lines).
2. **New section** "Status as of 2026-04-25": one paragraph noting
   that AbelianU1 closed unconditionally, F3 frontier is the new
   active target, link to `BLUEPRINT_F3Count.md` and
   `BLUEPRINT_F3Mayer.md`.
3. Section 3 Layer 4 ("Kotecky-Preiss cluster expansion") **as
   archived design reference** with header note: "These constructions
   were redirected into the F3-Mayer + F3-Count blueprints. See those
   for the current execution plan."
4. Section 6 (continuum-limit caveat) verbatim.
5. Section 7 (references) verbatim.

Deleted: Sections 1, 2, 4, 5; Layers 0–3 and Layer 5 of Section 3.

If approved by Lluis, Cowork agent can execute the trim in the next
turn.

---

## 6. Other deadweight candidates surfaced by the audit

Three areas worth flagging beyond Peter–Weyl:

### 6.1 `ClayYangMillsTheorem` and `ClayYangMillsStrong`

`ClayTrivialityAudit.lean` records, as Lean theorems, the fact that
both are logically equivalent to `True`. The repo has multiple
witnesses for these (across various files). **All witnesses for the
vacuous endpoints are now redundant** with the audit. Suggest:

- Keep one canonical witness file as a sanity check.
- Mark all other vacuous-endpoint witnesses with `@[deprecated]` and
  a docstring pointing to `ClayTrivialityAudit.lean`.
- Estimate: this would prune 200–600 lines of vestigial vacuous-
  witness code across the repo.

### 6.2 `CharacterExpansionData.{Rep, character, coeff}` PUnit/0/0 fillers

The reclassification record states these are filled with `PUnit / 0 / 0`.
Since no consumer reads `Rep`, `character`, or `coeff`, these fields
themselves are deadweight. Two options:

- **Aggressive**: drop the fields. `CharacterExpansionData` becomes
  a wrapper for `h_correlator : ClusterCorrelatorBound N_c r C_clust`
  only. Renames to `ClusterCorrelatorEnvelope` or similar to reflect
  reduced scope.
- **Conservative**: keep the fields but mark with a `@[deprecated]`
  attribute documenting they are vestigial.

The aggressive option saves ~50 lines and clarifies the API. The
conservative option preserves backward compatibility with any
external code that might pattern-match on the structure (probably
none, but worth a grep before deciding).

### 6.3 N_c=1 special case proliferation

`AbelianU1Unconditional.lean` is the load-bearing N_c=1 witness.
`AbelianU1Witness.lean` and `ConnectedCorrDecay.lean` both import it
and produce wrappers. Verify no third file reproduces the same content
under a different name; if it does, deduplicate.

---

## 7. Action items

For Lluis (human review):

- [ ] Approve trim of `PETER_WEYL_ROADMAP.md` per §5 (yes / no / modify).
- [ ] Decide aggressive vs conservative for `CharacterExpansionData`
      vestigial fields (§6.2).
- [ ] Decide whether to deprecate the redundant vacuous-endpoint
      witnesses (§6.1).

For Codex (autonomous, if approved):

- [ ] Execute approved trim (§5).
- [ ] Apply approved option from §6.2.
- [ ] Add `@[deprecated]` markers per §6.1, with a single canonical
      audit reference.

For Cowork agent (next turn):

- [ ] Produce `MATHLIB_GAPS.md` (Task #7).

---

*End of audit. Last updated 2026-04-25.*
