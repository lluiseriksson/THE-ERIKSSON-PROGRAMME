# C6c.8f3f localized retained prefixes — PRE-VALIDATION manifest

Status: scratch only. No `.olean`, focal build or axiom-oracle verdict exists.
Nothing in this manifest changes the `20/41` counter, constructs a
`TermSource`, or reaches window 15.

## Candidate pair

```text
2818165FE0F2779515EC524AEB1ACF947C16E361999BAC4C80E21BBFE2EBB624  tmp/BalabanCMP99SourceLocalizedRetainedTower.draft.lean
5C410626909A2AACCB7AE484BB7E3D84FA23C9B70A6822286D307C4EC61F4DE5  tmp/BalabanCMP99SourceLocalizedRetainedTowerAudit.draft.lean
```

## Contract

- One private recursion constructs the local and canonical prefix families.
- Prefix zero, prefix depth, every Qprime equality and both terminal
  identifications are derived inside the constructor.
- The canonical comparison background is the f3e identity extension generated
  from the exact retained carrier.
- The caller supplies no extension, prefix family, next-background equality or
  Qprime equality.
- The terminal theorem is a projection of equality at every prefix, not a
  separately assumed endpoint.

## Static gate

```text
F3F-TEXT-GATE=PASS FILES=2
```

The gate checks the PRE-VALIDATION marker, import order, absence of
`sorry`/`admit`, and textual delimiter balance. It is not compiler evidence.
