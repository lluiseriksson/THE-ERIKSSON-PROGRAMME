# hRpoly — current research status

[YangMills](../YangMills/README.md) · [News](../NEWS.md) · [Documentation](README.md) · [Active PR #29](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/29)

**Reviewed: 5 September 2026.** This is a curated reading guide to a fixed
public branch snapshot. It summarizes existing verification records; this
documentation update does not certify a new mathematical result.

## The problem in plain language

hRpoly is the missing estimate controlling how quickly the actual
Yang–Mills remainder activities decay in a cluster expansion with holes.
The programme must construct that estimate for the physical gauge
renormalization-group operator, then supply it to the existing consumers.
An interface that accepts the desired bound as an input does not prove it.

Recent work has made the physical objects, source dictionaries and remaining
obligations more explicit. The full physical activity bound is still open.
So are the four-dimensional continuum limit and OS/Wightman reconstruction.
The repository's historical Clay-distance shorthand remains **~0% (<0.1%)**,
not a measured completion percentage.

## At a glance

| Checkpoint item | Recorded status | What the number or label means |
|---|---|---|
| Terminal `PreEq136` producers | **20/41** | Source-facing producers in one finite checklist; intermediate adapters do not increment it |
| Constructed `TermSource` inhabitants | **0** | A conditional constructor receiving the missing data does not count |
| Physical window 15 | **Compatible; not attained** | The physical estimates still have to realize the scalar regime |
| Uniform physical `B0, delta0` | **Open** | One positive pair uniform in depth for the required physical actions |
| Physical `hraw → H# → hprofile` chain | **Open** | The final exponential profile must be produced, not assumed |
| PR #29 | **Draft** | Full closure, final reproduction and the terminal manuscript remain pending |

These are construction milestones, not a probability of success. Consult the
[pinned Definition of Done][dod] for every required row and its scope.

## Recent developments

All items below are **on the research branch**, not newly integrated into
`main`. “Cold-sealed” describes the cited record's fresh-checkout validation
of the named source/audit modules; it does not imply terminal reproduction of
the entire programme.

| Date (UTC) | Development | Evidence and limit |
|---|---|---|
| 2026-09-05 | Source-flow full-Green residue and owner identities recorded as cold-sealed | [Ledger, Addendum 1111][ledger]: source `bab82db7`, two focals and four audited declarations. Retains source coefficient/depth-dependent amplitude and `R^-4` normalization; no uniform physical bound |
| 2026-09-05 | Hybrid amplitude inequality passed its diagnostic | [Ledger, Addendum 1113][ledger]: source `9dafedaa`, `DIAGNOSTIC_FINAL_STATUS=PASS`, `COLD_SEAL=0`. The full uniform F4 endpoint remains unsealed |
| 2026-09-05 | Physical spacing and fibre-norm obligations made explicit | [Signature audit commit][spacing]: the value-only derivative adapter does not directly yield the required physical uniformity. This is a static audit, not a new theorem or a no-go for the physical estimate |
| 2026-09-04 | Source-flow scalar foundations and inverse uniqueness recorded as cold-sealed | [Ledger, Addendum 1109][ledger]: source `098cf3df`, five audited declarations; provides the source-specific full-Green foundation |
| 2026-09-04 | Arbitrary-residue and owner transport recorded as cold-sealed | [Ledger, Addenda 1107–1108][ledger]: sources `eef777d3` and `ea524400`; scoped transport results, not the terminal `B0, delta0` pair |

Failed and incomplete attempts are also preserved. In particular, Addendum
1114 records a composition diagnostic stopped by import-path shadowing;
the downstream uniform draft was not run. A repaired runner does not itself
validate that draft. The hard counters above did not move with these entries.

## What comes next

1. **Complete the uniform full-Green amplitude step (F4).** Check the exact
   composed endpoint and its hypotheses, then obtain the scoped cold evidence.
2. **Close physical regional transport (F5).** Preserve fibre norms, endpoint
   orientation and literal lattice spacing. The current value-only adapter
   introduces depth-dependent derivative costs under physical specialization;
   a complete rescaling dictionary or direct derivative estimates are needed.
3. **Produce one uniform physical `B0, delta0` pair and attain window 15.**
   Per-depth or separately chosen action bounds do not discharge this target.
4. **Install the remaining terminal producers.** Reach 41/41 and construct an
   actual conditional `TermSource`, then discharge the physical Lemma-1
   certificate needed for its unconditional form.
5. **Close the physical decay chain and terminal application.** Supply the
   produced UV decay to the registered mass-gap consumer, complete the final
   build/oracle and two independent reproductions, and synchronize the paper.

This is the order of mathematical dependencies, not a delivery-date promise.
The [vertical slice][slice] gives the detailed source-to-consumer map.

## Source snapshot

| Record | Immutable reference |
|---|---|
| Public `main` inspected for this update | [`04f87347f3e4d46a05e77bc1c70855794e111477`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/04f87347f3e4d46a05e77bc1c70855794e111477), dated 2026-08-03 |
| PR #29 research snapshot inspected | [`7b068757bf0b49cd4fe1cdd82501fab808880aa4`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/7b068757bf0b49cd4fe1cdd82501fab808880aa4), dated 2026-09-05 |
| Completion requirements | [Definition of Done at that snapshot][dod] |
| Mathematical evidence | [Verification ledger at that snapshot][ledger] |
| Source and consumer relationships | [Vertical slice at that snapshot][slice] |
| Canonical `main` proof-state contract | [`project-state.json`](../project-state.json); retained as recorded, not updated from branch build counts |
| Earlier hRpoly reduction paper | [PR #28 and its v0.3 release record](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/28); an earlier reduction, not the completed hRpoly paper |

The branch and its PR may advance after this review. Use the immutable links
to reproduce the statements on this page, and the [live PR][pr] for newer
activity. Build-job counts belong to individual commands and commits; they
are neither a progress metric nor interchangeable with the canonical main
record. This page does not reconcile or overwrite older build snapshots.

## Keeping this page useful

Update it when evidence changes a named milestone or exposes a new obstacle.
For each entry include the UTC date, exact source commit, ledger addendum,
verification scope and remaining limitation. Refresh the snapshot and counters
from the same evidence, add a short item to [NEWS.md](../NEWS.md), and keep the
summary in [YangMills](../YangMills/README.md) consistent. Retain failed records
and immutable references; a new date alone is not a research update.

[pr]: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/29
[dod]: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/7b068757bf0b49cd4fe1cdd82501fab808880aa4/docs/HRPOLY-END-TO-END-DOD-CHECKLIST.md
[ledger]: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/7b068757bf0b49cd4fe1cdd82501fab808880aa4/docs/VERIFICATION-LEDGER.md
[slice]: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/7b068757bf0b49cd4fe1cdd82501fab808880aa4/docs/HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md
[spacing]: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/7b068757bf0b49cd4fe1cdd82501fab808880aa4
