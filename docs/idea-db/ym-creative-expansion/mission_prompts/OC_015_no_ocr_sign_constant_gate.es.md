# Prompt de misión — OC_015_no_ocr_sign_constant_gate

Misión: Prevent any sign, exponent, summation domain or constant from being fixed from OCR-only text.

Proof card: `source-safety-ocr-gate`

Source keys permitidas:
- `AGENT-CHECKLISTS.md`
- `SOURCE-CLAIM-AUDIT.md`

Target shape:

```text
formula_component -> evidence_kind; OCR-only components must remain blockers
```

Éxito mínimo:

```text
Patch intake declares zero ocr_constant_uses or explains the blocker.
```

Rechaza si:
- OCR-only formula is promoted
- render/visual check absent for a sign or exponent

Entrega un patch intake JSON. No añadas consumidores downstream si no hay delta
positivo real.
