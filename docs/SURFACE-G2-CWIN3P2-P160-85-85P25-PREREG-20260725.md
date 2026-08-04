# Diagnostic preregistration: 160-bit scaled bulk on `[85,85.25]`

The authoritative CWIN=`3/2` high split at 180 bits timed out on this unit,
and the order-40/45 rescue at 220 bits also timed out on a narrower unit.  This
diagnostic freezes a lower-precision *candidate experiment* to distinguish
arithmetic cancellation from a geometric sign failure.  It keeps order 30,
t-order 37, the five explicit `t` partitions, and `min_dt=1/100000`, changing
only Arb precision to 160 bits.

The result is not admissible for G2: if it finishes, production/replay,
dependency hashes, and a dedicated validator are still required, and the
authoritative 180-bit rerun must pass before any promotion.  A timeout or a
nonnegative row is recorded as design evidence only.

