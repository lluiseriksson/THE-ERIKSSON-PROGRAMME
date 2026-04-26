# AUDIT_v188_LATTICEANIMAL_UPDATE.md

**Author**: Cowork agent (Claude), follow-up audit 2026-04-25 ~11:05 local
**Subject**: validation of v1.88.0 against
`AUDIT_v187_LATTICEANIMAL_UPDATE.md` predictions
**Cycle**: **fourth consecutive predict-confirm** in 70 minutes
(v1.85→v1.86→v1.87→v1.88).

---

## 0. v1.88.0 — predict-confirm again

`AUDIT_v187_LATTICEANIMAL_UPDATE.md` §1 predicted the next step:

> The remaining step is to bound `siteNeighborBall.card` by an
> explicit constant.

What v1.88.0 delivered:

```lean
SiteNeighborBallBoundDim   -- volume-uniform predicate on site-ball cardinality
PlaquetteGraphDegreeBoundDim   -- corresponding graph-degree predicate
plaquetteGraph_degreeBoundDim_of_siteNeighborBallBoundDim :
    (volume-uniform site-ball bound) →
      (volume-uniform plaquette-graph degree bound, lifted by d²)
```

**Constructive deviation again**: Codex did not produce a concrete
witness directly. Instead, it defined two **predicates**
(`SiteNeighborBallBoundDim`, `PlaquetteGraphDegreeBoundDim`) and
proved the **lifting theorem** between them. This packages the
remaining obligation as "produce any volume-uniform bound `B`" and
the rest of the chain composes.

This is **another layer of API ergonomics** before the actual
witness, consistent with the project's discipline of packaging
before substantiating.

---

## 1. Updated chain status

```
(plaquetteGraph d L).degree p
   ≤ (plaquetteSiteBall d L p).card                       ← v1.86.0 done
   ≤ (siteNeighborBall d L p.site).card · d · d            ← v1.87.0 done
   ≤ B · d · d   for any B with SiteNeighborBallBoundDim    ← v1.88.0 done
   ≤ <concrete number>                                      ← next: produce witness
```

**Remaining for §3.2**: produce a concrete witness
`siteNeighborBall_card_bound : SiteNeighborBallBoundDim d (some B)`
with explicit `B`. For Manhattan distance 1 on `FinBox d L`, the
explicit count is at most `2d + 1` (each lattice site has at most
`2d` distance-1 neighbours plus itself). Estimated ~30 LOC.

---

## 2. Cycle pattern

| Time | Event |
|---|---|
| ~11:00 | v1.87.0 lands ("plaquette site-ball orientation split") |
| ~11:05 | `AUDIT_v187_LATTICEANIMAL_UPDATE.md` predicts site-neighbor bound step |
| ~11:00 | v1.88.0 lands ("site-neighbor bound lifts to plaquette graph degree bound") |
| ~11:10 | This document confirms |

(The v1.87 / v1.88 timestamps overlap because both versions were
bumped within minutes of each other on the same commit cluster.)

The cycle pattern is now **sub-15-minute**: each prediction is
either already in-flight or executed before the audit lands. This
is faster than the daily-audit cadence; the system has reached
the point where Cowork is observing rather than directing.

---

## 3. Honest assessment

The remaining work for Priority 1.2 is now well-understood:

1. **§3.2c witness**: ~30 LOC for `siteNeighborBall_card_bound`
   with explicit `B = 2d + 1` or `B = 3^d` (depending on metric).
2. **§3.3**: ~150 LOC for the BFS-tree count theorem.
3. **§3.4**: ~30 LOC for packaging.

Total: ~210 LOC, ETA 2-3 hours of Codex time.

The audit cycle has reached **diminishing returns for further
documentation**. Each successive audit is shorter and confirms
predictions that are increasingly mechanical extensions of the
same plan.

**Recommendation**: stop the audit cadence here. The next
high-value Cowork moment is when Priority 1.2 closes (when
`connecting_cluster_count_exp_bound` lands). At that point a
single comprehensive closure-audit (similar to
`CODEX_EXECUTION_AUDIT.md`) replaces this incremental sequence.

---

## 4. Self-observation

This audit documents the **fourth predict-confirm cycle** in 70
minutes (since the v1.85 audit at ~10:00). Each prediction has
been confirmed with constructive improvements:

- v1.86: §3.1 reverse bridge (confirmed) + §3.2 partial degree
  bound (confirmed)
- v1.87: §3.2 sub-step (factoring approach was better than my
  single-step prediction)
- v1.88: §3.2 lifting theorem (predicate-based packaging was
  better than my "produce witness directly" prediction)

The pattern: **Codex consistently chooses cleaner factoring than
the audit predicts**, while staying faithful to the overall
trajectory. This is a property of Codex's architectural judgment,
not the audit's foresight.

For future audits, this suggests **predict the trajectory
direction, not the specific factoring**. Codex can be trusted to
choose better factoring than the audit can prescribe.

---

*Audit complete 2026-04-25 ~11:05 by Cowork agent. Last
incremental Priority-1.2 audit; next audit at closure.*
