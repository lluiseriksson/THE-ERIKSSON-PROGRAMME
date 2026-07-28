# Fable terminal-relay audit

Date: 2026-07-28

Profile selected explicitly: `masterythief`

Expected and authenticated account: `masterythief@gmail.com`

Verified principal model: `claude-fable-5`

## Scope

The audit was deliberately limited to the logical relay for
`beta >= 1000/9`, assuming the stated interval certificates as premises.  It
checked:

- the closed union of the three edge lanes through `lambda=3`;
- the sign transfer from `-E_t/lambda>0`;
- the exact identity
  `E'/(-sin(t/2)/2)=Q+X_full`;
- the two `p=sin(t/4)` lanes;
- the arithmetic margins `19/20-10^-30-1/100000` and
  `19/20-9/10-1/100000`;
- the delta/K2 domain split.

## Result and amendment

Fable judged the arithmetic, signs, and domain union valid under the stated
premises.  It found one genuine editorial ambiguity: the proof alternated
between `E_t` and `E'` without explicitly identifying the notation.  It also
recommended saying that K2 is used only in the `lambda>=3` branch.

The manuscript now states
`E_t=partial_t E=E'` and explicitly restricts the K2 use to that branch.
These are clarification edits, not changes to a certificate or theorem.

The bridge reported `verified_model: "claude-fable-5"` and no error.  A
small auxiliary Haiku usage reported by the bridge was not used as a
fallback; the principal answer was verified as Fable 5.  The conclusion was
then checked independently against the manuscript identity and executable
domain audits before application.
