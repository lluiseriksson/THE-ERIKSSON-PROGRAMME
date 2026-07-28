# Unit-82 rescue cover completed (normalized sign only)

**Status:** quarantined candidate; no G2/G6 or `(H_tail)` promotion.

The original order-24 unit `[275/4,69]` failed at the minimum `t` step.  The
order-30/35 rescue protocol now exhausts that beta unit in three adjacent
slices:

```text
[275/4,1101/16] : 167 rows
[1101/16,1103/16] : 172 rows
[1103/16,69] : 167 rows
```

All 506 rows are strictly negative for the normalized `W^J` predicate, and
each production transcript has a byte-identical replay.  The combined
manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-unit82-rescue-order30-combined-20260723.json`.

This closes only a finite normalized-sign cover.  It does not establish the
absolute relay to `(H_tail)`, supply `M_supremum`, or change the authoritative
G2/G6 gates.  The positive rescaling identity preserves the Wronskian sign,
so the missing weighted tail lemma remains logically independent.
