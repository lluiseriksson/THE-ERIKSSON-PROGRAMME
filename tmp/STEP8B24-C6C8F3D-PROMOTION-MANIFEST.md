# C6c.8f3d canonical-extension comparison — PRE-VALIDATION manifest

Status: scratch only. No `.olean`, focal build or axiom-oracle verdict exists.
Nothing in this manifest changes the `20/41` counter, constructs a
`TermSource`, or reaches window 15.

## Candidate pair

```text
D342CF65C8E0A6DB0AD5691EED3110493C369631ABCA3F57545F106D3E4DCBA1  tmp/BalabanCMP99SourceLocalizedTowerCanonicalExtension.draft.lean
7555D88DE4640BE8A45088F8C9E6CFDB782AB03FAD21E789B7172252A3DF2709  tmp/BalabanCMP99SourceLocalizedTowerCanonicalExtensionAudit.draft.lean
```

## Contract

- The local background is small only on the recursively generated retained
  fine read carrier.
- The comparison target is the literal canonical source tower of a globally
  admissible extension, not a caller-selected tower.
- Agreement between local and global backgrounds is required only on that
  retained carrier.
- The proof constructs the head-average and selected next-background
  equalities internally; it does not accept a complete next-background or
  Qprime equality.
- The localized/canonical selected-bond bridge reduces both values to the
  literal raw Ubar expression.

## Static gate

```text
F3D-TEXT-GATE=PASS FILES=2
```

The gate checks the PRE-VALIDATION marker, import order, absence of
`sorry`/`admit`, and textual delimiter balance. It is not compiler evidence.
