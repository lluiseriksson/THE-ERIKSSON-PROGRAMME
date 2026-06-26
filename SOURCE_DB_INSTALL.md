# Instalación en THE-ERIKSSON-PROGRAMME

Copiar sobre la raíz de la repo:

```text
docs/source-db/
scripts/source_db.py
tests/test_source_db.py
AGENT_BUILDER_PROMPT.md
source-packets/
```

No copies `docs/source-db/examples/cmp116-current-seed.json` a `docs/source-citations/`: solo permite que este ZIP funcione de forma independiente. En la repo real, `scripts/source_db.py` detecta automáticamente el catálogo existente `docs/source-citations/cmp116-lemma3.json` y omite el seed de ejemplo.

Después:

```powershell
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py coverage
```

Configura el directorio privado de originales:

```powershell
$env:YM_SOURCE_ROOT = "C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary"
python scripts\source_db.py verify --check-local
```

Para crear el ZIP privado acumulativo:

```powershell
python scripts\source_db.py packet --include-raw --output source-packets\out\ym-source-packet.zip
```

Antes de cada commit:

```powershell
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py blockers
python scripts\check_consistency.py
lake build YangMillsCore
lake env lean oracle_check.lean
```
