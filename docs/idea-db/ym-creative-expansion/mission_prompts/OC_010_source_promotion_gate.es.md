# Prompt de misión — OC_010_source_promotion_gate

Misión: Promote a citation/status only after exact locator, formula, assumptions, dictionary, Lean targets and downstream-only open questions are present.

Proof card: `proof.source-status-promotion.gates`

Source keys permitidas:
- `docs.SOURCE-CITATIONS`
- `docs.source-db.README`

Target shape:

```text
source_pending -> source_extracted or lean_linked -> theorem_checked only with required evidence
```

Éxito mínimo:

```text
One source-lock worksheet complete and a patch intake declaring source_promotions >= 1.
```

Rechaza si:
- promotion relies on OCR-only formula
- open questions still include the extracted theorem itself
- no Lean target linked

Entrega un patch intake JSON. No añadas consumidores downstream si no hay delta
positivo real.
