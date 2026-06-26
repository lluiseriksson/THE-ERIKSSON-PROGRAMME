# Prompt de misión — OC_011_router_sync_for_source_key

Misión: When a source key is used, verify it maps to exactly the intended proof card and Lean targets before patching.

Proof card: `source-key-router-sync`

Source keys permitidas:
- `SOURCE-KEY-ROUTER.md`
- `PROOF-OBLIGATION-CARDS.md`

Target shape:

```text
source_key -> proof_card -> mission_contract -> lean_targets
```

Éxito mínimo:

```text
Router sync table updated or confirmed with no orphaned source key.
```

Rechaza si:
- source key touches multiple proof cards but patch combines them
- new citation key lacks router entry

Entrega un patch intake JSON. No añadas consumidores downstream si no hay delta
positivo real.
