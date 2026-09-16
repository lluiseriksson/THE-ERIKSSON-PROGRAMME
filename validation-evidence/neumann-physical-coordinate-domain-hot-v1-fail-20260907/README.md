# R5 physical domain HOT v1 — FAIL retained

Source: `7d719ad27d4c5a6a0526bd3748cc24367586b432`.
Runner: `2cb7f1bce53b0cb1b1f88e4a5195bb8437964864`.
Archive SHA-256: `a945490226ec6c27224a0edd41e83a8fd43ca393abd27c40cc5a504cb2e613b0`.

First error: `NeumannPhysicalCoordinateReflectionDomainDraft.lean:61:13: error: typeclass instance problem is stuck`, `NeZero ?m.80`.
Prerequisites exit 0 (41.533344204 s); physical exit 1 (7.185009505 s).
The second printed declaration contains `sorryAx` from failed elaboration: this is FAIL, not an axiom gate PASS. No output is accepted.

Minimal proposed repair: explicitly supply `(L := L) (j := j)` in the reflected-domain call. No statement, hypothesis, or constant changes. HOT diagnostic only; counters remain 20/41, TermSource 0, window 15 open.
