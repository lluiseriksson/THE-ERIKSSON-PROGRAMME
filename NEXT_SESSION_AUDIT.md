# NEXT_SESSION_AUDIT.md

**Author**: Cowork agent (Claude), staleness audit 2026-04-25
**Subject**: `YangMills/ClayCore/NEXT_SESSION.md` (773 lines)
**Method**: section-by-section read; identify content that
contradicts the post-v1.79 reality (Resolution C, exponential
frontier, packaged Clay route)

---

## 0. Bottom line

NEXT_SESSION.md is **partially stale**. Specifically:

- The **intro section** (lines 1-60) presents the **polynomial**
  packages (`ShiftedF3MayerCountPackage`,
  `PhysicalOnlyShiftedF3MayerCountPackage`) as the "preferred"
  route. After Resolution C, the **exponential** package
  `ShiftedF3MayerCountPackageExp` (v1.82.0) is the canonical
  closure target, not the polynomial one.

- The **"Two Mathematical Subtargets" section** (lines 451-705)
  describes:
  - **F3-Mayer subtarget** (line 453): asks for
    `ConnectedCardDecayMayerData` with bound
    `|K| ≤ if PolymerConnected then A₀ * wab.r^|Y| else 0`. This
    statement is **current** for the activity-side, but the
    references to `ShiftedF3MayerPackage` and
    `ShiftedF3MayerCountPackage` are the polynomial-route names.
    Should reference `ShiftedF3MayerPackageExp` and
    `ShiftedF3MayerCountPackageExp`.
  - **F3-Count subtarget** (line 501): asks Codex to produce
    `ShiftedConnectingClusterCountBound C_conn dim` — which is
    the **polynomial frontier** that `COWORK_FINDINGS.md`
    Finding 001 established as **structurally infeasible**. This
    section is **misleading** — Codex reading it could be
    redirected back to the polynomial route.

- The **mid-document exponential interface** (lines 615+) **does**
  describe `ShiftedConnectingClusterCountBoundExp` and the
  v1.82.0 package. So the document contains both perspectives
  side-by-side without a clear "use this one" signal.

This is **the most important staleness in the strategic doc set**
because NEXT_SESSION.md is consumed directly by the autonomous
Codex daemon on each session start. A stale or contradictory
NEXT_SESSION can lead to wasted Codex effort.

---

## 1. The contradiction surfaced

The intro opening (lines 7-15) says:

> The preferred single-object F3 frontier is:
>
>     ShiftedF3MayerCountPackage N_c wab
>
> in `YangMills/ClayCore/ClusterRpowBridge.lean`.

But the v1.82.0 release added `ShiftedF3MayerCountPackageExp`,
which is now the natural closure target. The intro should reflect
this.

Later in the document (lines 658-676), Codex's own update added:

> The packaged version to target in new F3 work is:
>
>     ShiftedF3MayerCountPackageExp N_c wab
>
> ...
> For separately produced halves, use
> `ShiftedF3MayerCountPackageExp.ofSubpackages mayer count hKr_lt1`.

So the document **knows** the exponential route is preferred but
the intro hasn't been updated to match.

Similarly, the F3-Count subtarget section (line 501) still asks for
the polynomial bound. Since the same document elsewhere (line
615+) describes the exponential interface, the subtarget framing
is internally inconsistent.

---

## 2. Recommended changes

### High priority — F3-Count subtarget reframe

Edit lines 501-705 to:

1. **State the target as `ShiftedConnectingClusterCountBoundExp 1 K`**
   (with `K = 2d-1 = 7` tight or `K = 4d² = 64` loose).
2. **Remove or footnote the polynomial-frontier sketch** that
   currently dominates the subtarget. Cross-reference
   `BLUEPRINT_F3Count.md` §−1 (the Resolution C update overlay)
   for the rationale.
3. **Mention `LatticeAnimalCount.lean`** as the file where the
   v1.85.0 work has begun, and reference
   `AUDIT_v185_LATTICEANIMAL.md` for the breakdown of remaining
   sub-steps (3.1 reverse bridge, 3.2 degree bound, 3.3 BFS-tree
   count, 3.4 packaging).

Estimated edit: ~50 lines reformatted, 80 lines of polynomial
material moved to a "historical" footer or deleted.

### Medium priority — intro reframe

Edit lines 1-60 to:

1. **Promote the exponential package** to "preferred frontier":

   ```
   The active Clay-critical front is no longer L2.6 / Peter-Weyl.
   The consumer-driven target is:

       ClusterCorrelatorBound N_c r C_clust

   The preferred single-object F3 frontier (from v1.82.0) is:

       ShiftedF3MayerCountPackageExp N_c wab

   in `YangMills/ClayCore/ClusterRpowBridge.lean`. It bundles
   exactly:

       data    : ConnectedCardDecayMayerData N_c wab.r A₀ ...
       h_count : ShiftedConnectingClusterCountBoundExp C_conn K
       hKr_lt1 : K * wab.r < 1

   and feeds directly into:

       clayMassGap_of_shiftedF3MayerCountPackageExp →
           ClayYangMillsMassGap N_c
   ```

2. **Demote the polynomial package** to a "legacy / backwards-compatible"
   footer note.

### Low priority — F3-Mayer subtarget alignment

The F3-Mayer subtarget descriptions (lines 453-499) are mostly
correct on the math. They reference `ShiftedF3MayerPackage` (the
polynomial-route name); should also reference the exponential
counterpart for consistency.

---

## 3. Why this matters

NEXT_SESSION.md is **the single document Codex reads to decide what
to work on next**. Per `CONTRIBUTING_FOR_AGENTS.md` §0, it's in
the read-on-session-start checklist.

If NEXT_SESSION.md leads Codex back to the polynomial F3-Count
route, days of wasted effort on a structurally infeasible target
are possible. Even if Codex's contextual judgment is good (it has
been so far — v1.85.0 is correctly working on the
exponential-frontier Klarner BFS-tree), an over-eager session
might reach for the polynomial sketch in NEXT_SESSION.md as the
"explicit instruction" and follow it.

Risk severity per `THREAT_MODEL.md`: medium (process / governance
failure mode similar to §2.1 canary-spam loop).

---

## 4. Cross-checks

### 4.1 Has Codex actually started polynomial work since Resolution C?

Quick `git log` audit:

```
Past 24h commits with "polynomial" or "polyN" or
"ShiftedConnectingClusterCountBound" but NOT "Exp":

(none found that suggest active polynomial-frontier work)
```

Codex has been correctly attacking the exponential frontier
(v1.79-v1.85). NEXT_SESSION.md staleness has not produced harm
**yet**, but the risk remains for a future session.

### 4.2 Is BLUEPRINT_F3Count.md §−1 visible enough?

Yes — both blueprints have the §−1 update overlay at the very top
of the document, so any agent reading them encounters the
Resolution C status before the body content. This is the saving
grace.

But Codex doesn't necessarily re-read BLUEPRINT_F3Count.md every
session — `CONTRIBUTING_FOR_AGENTS.md` §1 lists the blueprint as
"if you have time, also skim". The contract expects
NEXT_SESSION.md as primary.

So **fixing NEXT_SESSION.md is the higher-leverage action** than
expecting Codex to defensively cross-read blueprints.

---

## 5. Recommendation

Either:

- **Option A (proper edit)**: Cowork agent or Lluis or Codex
  performs the reframe described in §2 above, replacing the
  polynomial-frontier subtargets with exponential-frontier
  language. Estimated 30-60 minutes of editing.

- **Option B (banner only)**: Add a banner at the top of
  NEXT_SESSION.md saying:

  ```
  > **Update 2026-04-25 (post-v1.82.0)**: the **exponential**
  > frontier `ShiftedF3MayerCountPackageExp` (v1.82.0) is the
  > current closure target. The polynomial-frontier descriptions
  > in this document below are kept for backwards compatibility
  > but are NOT the active work surface. Refer to
  > `BLUEPRINT_F3Count.md` §−1 for Resolution C and the active
  > priority queue.
  ```

  Estimated 5 minutes.

**Cowork recommendation**: **Option B for now, Option A in the
next routine maintenance pass**. Option B prevents the staleness
from being actively harmful immediately, and is fast enough that
it can ship in this session if Lluis approves.

---

## 6. Aside: where the F3-Mayer subtarget framing IS still useful

Lines 453-499 (the F3-Mayer subtarget section) describe what's
already closed at the single-plaquette layer:

```
singlePlaquetteZ_pos
plaquetteFluctuationNorm_integrable
plaquetteFluctuationNorm_mean_zero
plaquetteFluctuationNorm_zero_beta
```

This is current and useful. The remaining F3-Mayer work
described — "the product-measure / polymer lift to
ConnectedCardDecayMayerData" — is **exactly** what
`BLUEPRINT_F3Mayer.md` plans across files
`MayerInterpolation.lean`, `HaarFactorization.lean`,
`BrydgesKennedyEstimate.lean`, `PhysicalConnectedCardDecayWitness.lean`.

So the F3-Mayer subtarget framing is **conceptually right**, just
outdated on the package-name level. Quick edit suffices; no
rewrite needed.

---

*NEXT_SESSION audit complete 2026-04-25 by Cowork agent.*
