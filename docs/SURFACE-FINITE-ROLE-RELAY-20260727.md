# Surface finite-beta role relay

**State:** `FINITE_ROLE_PROVED`

This record binds the already certified range witnesses to the exact
Wronskian algebra.  It closes the logical relay on

```text
20 <= beta <= 1000/9,   0 < t < pi.
```

It is intentionally independent of K2 and of the obsolete split-tail
hypothesis `(H_tail)`.

## Partition

| t range | witness |
|---|---|
| `0<t<=3/5` | certified G4 scaled-left union |
| `3/5<=t<=pi-3/(2 beta)` | exact-union scaled bulk cover |
| `pi-3/(2 beta)<=t<pi` | certified G5 union |

The authoritative bulk audit checks strict negative upper endpoints,
production/replay equality, output hashes, exact rational beta union, the
moving seam at each box's **upper** beta endpoint, and an adjacent canonical
ownership subcover.  It reports the exact beta component `[20,1000/9]` with
no gap.

The historical scaled-left transcripts record partition-helper digest
`3abc0499...`, whose exact source bytes are no longer present.  The validator
does not pretend otherwise: it pins that recorded digest, verifies every
other dependency byte-for-byte modulo EOL normalization, and reconstructs
the complete 912-interval rational partition independently from all 4,636
certified rows in both production and replay.  Thus this is a source-archive
limitation, not an uncovered mathematical interval.

## Exact implication

Theorem A gives `F_B>0`.  Exact differentiation and the common positive
family scaling give

```text
W = 4 F_B^2 E',
W_scaled = positive_factor * W.
```

Therefore every strict `W_scaled<0` certificate implies `E'<0`.  Since the
three t ranges above cover `(0,pi)`, the finite-beta conclusion follows.

The executable role audit is
`scripts/audit_surface_finite_role_relay.py`.  It imports and reruns the
authoritative union audit, the production/replay validators for the scaled
left edge and all three G5 blocks, the scaled-tail contract, and the
dependency-free sign algebra.  It also checks the exact Theorem A statement
in the manuscript.  The closure board is not an input to this proof.

The deterministic bulk ownership chain has 501 rows and the frozen terminal
fingerprint
`86029ed96f88c53fd0fe18769e33577d4eee56aed553f36943dd490f09b7ae80`.
That digest binds each ownership row to its manifest and to the LF-stable
bytes of both the production and replay transcript.  Raw hashes remain
checked against the recorded raw/LF/CRLF variants, so Git EOL normalization
cannot create a false provenance failure.

## Reproduction

```powershell
python scripts/audit_surface_finite_role_relay.py
python -m pytest -q tests/test_surface_finite_role_relay.py
```

This is a finite-range promotion only.  It does not promote K2, the
high-beta half-line, K4, S1'''/S2''', or the final paper seal.
