# Owner/point HOT v1 — verified FAIL with valid owner prefix

Draft source6f20ead457a528c2e5df6cc5fa2318fe43dbeeda over retained
checkout59f9f522f3f731ac8a6270ac5c3ae719b1b201f6. Same CPU/highRAM host685dabaa0a79.
Actual start2026-09-05T13:51:54.819662Z, PID18947. Diagnostic exit1 after
64.321446626s, stop-on-first-error, no cold rebuild and no rerun.

Outer SHA256 observed remotely and matched after browser download:
`977381b2359725c471b9c80401eccd933fdb162928126ce9f34f8aca20602b19`.
Inner SHA256:
`cea5571fea96a7ce138184cffddbca13dc724a0a1441de06f5f242ab3b79e01a`.

The downloaded pinned verifier accepted the FAIL prefix locally:
11stages,3exact allowed public axiom sets,3successful output hashes.
Measurement0.11925s,26,103,808peakbytes; one process, no Lean or network.
The original archives retain raw logs, exact source bytes and partial-output
classification. No declaration from the failed module is accepted.

Valid HOT prefix:

- Owner-cast Mathlib repro PASS.
- Point-probe Mathlib repro PASS.
- Incremental prerequisite build PASS.
- Owner dictionary PASS exit0/7.7130478s: site-map equality, block-owner
  equality, exact single-owner fibre cardinality `(L^(depth+1))^4`.
  Three exact standard axiom sets. One unused-section-variable warning
  on `[NeZero K] [NeZero Q]` remains; this is not a warning-free seal.

First error (verbatim):

```
tmp/SourceFlowPhysicalPointProbeDraft.lean:58:6: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
```

Point-probe child exit1/8.762927235s. The later `sorryAx` in its printed
axioms is elaborator error recovery, not accepted proof evidence and not
a source placeholder. The textual source guard passed; the failure is
project-specific inference of a positive carrier size.

Successful output SHA256:

- OwnerCastRepro: `03ea841c0896fa99039bffc53d45a105c72acadc1f0e14ced3afadc8ba10cfcf`.
- PhysicalOwnerDictionaryDraft: `461cb7a55af838dee1d1c9db549aa671a6a968b4c0a3383183594dc1a61e642a`.
- PointProbeRepro: `3aa498de4bde37595802018fac6eed6392a73e9276186ec96d7281f075ac0cd1`.

No Lean/Lake/launcher remained at13:56:06UTC. Runtime disconnected and
deleted about13:57UTC (about50min connected for both units), reconnect
state verified, only tab closed, monitor deleted. No remote job remains.
20/41,TermSource0,window15 unattained. This is HOT evidence, not promotion.
