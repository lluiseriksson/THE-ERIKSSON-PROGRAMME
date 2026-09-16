# C6c.8f3e retained fine extension — PRE-VALIDATION manifest

Status: scratch only. No `.olean`, focal build or axiom-oracle verdict exists.
Nothing in this manifest changes the `20/41` counter, constructs a
`TermSource`, or reaches window 15.

## Candidate pair

```text
4F11A4E2B29A5BB3D835E717A224BFABA44CFE009FB2882E216314F990928F5B  tmp/BalabanCMP99SourceRetainedFineExtension.draft.lean
F04CB5A0C105DCA9A515FB92ECE09DA3B5CC41B5A5743BADBB7E085516BDD403  tmp/BalabanCMP99SourceRetainedFineExtensionAudit.draft.lean
```

## Contract

- The extension is generated internally from the exact recursive retained
  carrier.
- It agrees with the local background on every retained positive coordinate.
- It is the identity on every unretained positive coordinate and uses the
  standard inverse convention on negative orientations.
- Global smallness is derived from local smallness and nonnegativity of the
  radius.
- The localized/canonical tower equality is specialized to this generated
  extension; no extension or equality is exposed at the source endpoint.

## Static gate

```text
F3E-TEXT-GATE=PASS FILES=2
```

The gate checks the PRE-VALIDATION marker, import order, absence of
`sorry`/`admit`, and textual delimiter balance. It is not compiler evidence.
