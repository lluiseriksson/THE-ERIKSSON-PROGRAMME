# Prompt de misión — OC_012_build_oracle_evidence_gate

Misión: Attach build/oracle evidence only after a Lean theorem is claimed to feed a former hypothesis.

Proof card: `build-oracle-evidence`

Source keys permitidas:
- `oracle_check.lean`
- `docs/VERIFICATION-LEDGER.md`

Target shape:

```text
theorem_name + removed premise + lake build + oracle output
```

Éxito mínimo:

```text
Patch intake contains verification_evidence.build and verification_evidence.oracle when theorem_checked_promotions > 0.
```

Rechaza si:
- build/oracle claimed without command output
- theorem does not feed the removed caller premise

Entrega un patch intake JSON. No añadas consumidores downstream si no hay delta
positivo real.
