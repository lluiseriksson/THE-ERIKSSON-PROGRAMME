# Prompt de misión — OC_013_exact_source_locator_lock

Misión: Lock exact printed/PDF page, equation range, render/local text and source-symbol dictionary before any formula promotion.

Proof card: `source-locator-lock`

Source keys permitidas:
- `all primary source keys`

Target shape:

```text
source key has locator + formula + assumptions + dictionary + use_for/do_not_use_for
```

Éxito mínimo:

```text
A source_locks/*.json worksheet with all required fields and no unknown constants.
```

Rechaza si:
- citation is only bibliographic
- formula has unstated quantifiers
- constants/exponents set from OCR

Entrega un patch intake JSON. No añadas consumidores downstream si no hay delta
positivo real.
