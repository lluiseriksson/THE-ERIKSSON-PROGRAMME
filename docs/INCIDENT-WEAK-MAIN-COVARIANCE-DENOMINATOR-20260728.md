# Incident — dependency-lost `KD**2` denominator (2026-07-28)

**Scope:** first weak-main covariance production attempt; no mathematical or
gate promotion.

The first production process was started with fresh output paths.  While it
was still running and both stdout/stderr were empty, an independent far-domain
design probe exposed that the expression

```text
moments["kd"]**2
```

used generic ball multiplication.  For a positive but wide ball `KD`, this
forgets that the two factors are identical.  On a reproduced design box,

```text
KD lower = 0.8017307696...
KD upper = 2.0459890821...
```

while the generic product enclosure included zero.  Division then returned
`nan`.  This is dependency loss in the instrument, not a mathematical
denominator zero.

The still-mute process was terminated.  Its two empty files are preserved as

```text
outputs/surface-k2-weak-main-covariance-nonterminal-denominator-20260728.txt
outputs/surface-k2-weak-main-covariance-nonterminal-denominator-20260728.stderr.txt
```

They are not evidence.

The repair uses monotonicity on the already certified positive interval:

```text
KD^2 in [KD_lower^2,KD_upper^2].
```

No partition, precision, companion order, tail charge, target, or acceptance
criterion is changed.  A fresh production path is mandatory.
