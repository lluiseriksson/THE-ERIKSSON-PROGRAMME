# Surface K4 global-judge audit

**Registered:** 2026-07-27

**State:** historical false green isolated; K4 remains unpromoted

## Result

The current K4 candidate rows are local Taylor-budget contributions, not
independent certificates.  The literal S1''' weight is

```text
2 |half-f'' box integral| *
integral_delta_lo^delta_hi (delta_final-u) du
------------------------------------------------
budget * delta_final^2
```

and therefore the fractions must be **summed over the complete delta
partition** before the `<1` judge is applied.

The executable audit reads the 39 current positive bands on
`delta=[61/2000,1/20]` and obtains:

```text
MD2r_mirror  1.65631183542785...  FAIL
MDFr_mirror  0.203674502480343... PASS
MD_mirror    0.917092905359875... PASS
MF_mirror    0.145995801963535... PASS
muF_main     3.77849982936977...  FAIL
nuD_main     4.92719161161887...  FAIL
nuF_main     4.57713074819412...  FAIL
```

Thus four of the seven global rows fail.  This is not a counterexample to
the Surface Theorem; it rejects the historical K4 budget architecture.

The domain is also disjoint from the live high-beta K2 lane:

```text
K4 positive rows: delta in [61/2000,1/20]
K2 high beta:     delta in [0,9/1000]
```

Consequently those K4 rows cannot discharge the live grouped bilinear
residual.

## False-green witness

The committed transcript
`scripts/surface_remainder_k4_tbox_delta0040_t225_230.txt` prints

```text
K4 CENTERED T-BOX PROBE PASS
```

while `MD2r_mirror>1` and `MD_mirror>1`.  Its actual configuration is
`t=[11/5,23/10]=[2.2,2.3]`, despite the filename's `t225_230` label.
It is retained as historical incident evidence and carries no theorem load.

The tracked t-box transcript driver now computes its terminal verdict from
the literal finite-and-`<1` predicate and returns a nonzero process status on
failure.  The predicate is centralized for successor drivers.  Historical
transcripts are not rewritten.

## Independent audit

Claude Opus 5 Max first identified the additive-judge and unconditional-PASS
defects in a read-only repository audit.  The result was accepted only after
the returned JSON reported `is_error=false` and `modelUsage` contained
exactly `claude-opus-5`.  Codex then independently checked the source,
recomputed all 39 sums with 200-bit Arb, and encoded the result in:

```text
python scripts/audit_surface_k4_global_judge.py
python -m pytest -q tests/test_surface_k4_global_judge_audit.py \
  tests/test_surface_k4_t_box_probe_verdict.py
```

No Fable result was used for this audit.
