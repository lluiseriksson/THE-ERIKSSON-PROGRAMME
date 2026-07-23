# Preregistration: CWIN=3/2 mid-cover order-24 extension 5

**Status:** `DESIGN_ONLY`; candidate sign evidence only. This extension cannot
promote G2/G6 or discharge `(H_tail)`.

The run extends the already isolated order-24 repair chain to the exact
rational beta units

```text
[259/4,65], [65,261/4], ..., [275/4,69]
```

using the unchanged mesh and stopping rule from the order-22 repair:

```text
CWIN       = 3/2
beta order = 24
t order    = 25
Arb        = 180 bits
min_dt     = 1/100000
beta width = 1/4
t domain   = [3/5, pi - (3/2)/beta_hi]
```

Each unit must emit a production transcript and an independent replay. The
validator must check current dependency hashes, exact beta adjacency, exact
per-unit t adjacency, strict outward-rounded negative upper bounds, and byte
identity of production/replay. A timeout, nonnegative enclosure, stale hash,
or missing row is a failure and leaves the unit uncovered. A successful chain
remains quarantined sign evidence: the separate finite-bridge relay lemma and
the global H-tail/K4 obligations are not supplied by this computation.
