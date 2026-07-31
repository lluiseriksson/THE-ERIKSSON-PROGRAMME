# R30 — independent Fable mathematics audit record

Date: 2026-07-31 (Europe/Stockholm)

Scope: bounded, read-only audit of the exact-trace repair and the
positivity-improving counterexample in the R30 erratum for `2602.0033`.

## Authentication and model attestation

- Selected bridge profile: `default`.
- Exact authenticated account reported by the profile: `luis.ebikeride@gmail.com`.
- Account selection was explicitly authorised by the owner as part of the rotating
  Fable accounts.
- Successful response: `isError = false`.
- Successful response: `verified_model = claude-fable-5`.
- The bridge's model-usage metadata included `claude-fable-5`; a small Haiku
  routing entry was also reported and is not represented as the principal audit.
- Principal-audit duration reported by the bridge: 134381 ms.
- No Opus result was requested or used.

This is a normalised audit record, not a purported byte-for-byte copy of the
bridge JSON response.

## Attempt log

1. The first attempt with profile `masterythief` failed with HTTP 429. It supplied
   no usable audit evidence.
2. A long request with profile `default` exceeded the 300-second outer tool limit.
   It supplied no usable audit evidence.
3. A bounded request with profile `default`, without repository-read tools and
   with a 240-second limit, completed with the attestation above. Only this third
   response is used as independent evidence.

## Independent finding

Verdict on the bounded mathematical question: **VALID**, subject to an important
precision requirement that is now explicit in the R30 source.

Let

`X_M = A_n(M) exp(-m_n(M) M)` and
`Y_M = A_(n+1)(M/2) exp(-m_(n+1)(M/2) M/2)`.

Under exact trace matching, subexponential first-excited multiplicities, and
excited tails that are `o(1)` *multiplicatively relative to their corresponding
first-excited term*, the repaired condition

`|Q_M - 1| = o(X_M + Y_M)`

implies `X_M - Y_M = o(X_M + Y_M)`. Positivity then gives `X_M / Y_M -> 1`.
Taking logarithms and using subexponential multiplicities gives the exponent
matching required for limiting gap doubling. The audit specifically rejected
interpreting the tail hypothesis as an additive absolute `o(1)`, which would be
too weak at exponentially small scales.

The independent audit also checked the positive two-level diagonal trace-class
construction with limiting gaps `a = 1/3` and `b = 1`. It satisfies the weaker
R29 limiting-scale normalisation condition and the exact trace identity while
violating both the repaired finite-scale condition and limiting doubling. Thus it
is a valid counterexample to the sufficiency claimed by R29.

## Local adoption and recheck

The multiplicative-relative-tail qualification and the strong exponent-matching
formula were propagated into `src/erratum_2602_0033.tex`. Local verification was
then rerun independently of Fable under Python optimisation levels 0 and 1; see
`VERIFY-TRANSCRIPT-O0.txt` and `VERIFY-TRANSCRIPT-O1.txt`.

This audit does not certify the remainder of the 25-page package, the visual
rendering, the provenance appendices, or the submission metadata. Those are
separate audit gates.
