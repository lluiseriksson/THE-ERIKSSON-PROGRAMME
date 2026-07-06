# Base de fuentes y fórmulas

Esta carpeta convierte los catálogos JSON de `docs/source-citations/` en un índice SQLite consultable sin volver a explorar artículos enteros.

## Principio de diseño

- **Fuente de verdad revisable:** JSON versionado en Git.
- **Índice rápido:** `docs/source-db/source_index.sqlite`, generado desde los JSON.
- **Artefactos primarios privados:** PDF, OCR completo y renders en `source-packets/private/`, fuera de Git.
- **Trazabilidad:** cada artefacto privado se identifica mediante ruta relativa, SHA-256 y manifiesto.
- **Honestidad matemática:** `visual_confirmed` no significa `source_extracted`, y una cita no se convierte en prueba hasta que el teorema Lean correspondiente compila y pasa el oracle check.

## Comandos

```powershell
python scripts\source_db.py build
python scripts\source_db.py verify
python scripts\source_db.py search "Eq. (2.31)"
python scripts\source_db.py show cmp116.eq231.p-bond-sum
python scripts\source_db.py lean CMP116Eq231PBondBoundary
python scripts\source_db.py blockers
python scripts\source_db.py frontier --term rawsource --status lean_linked
python scripts\source_db.py coverage
python scripts\source_db.py artifacts cammarota_cmp85
python scripts\source_db.py head-refs
```

`show <key>` also prints a `source acquisition` block for the key's direct
source when that source has registered web URLs or private artifacts, so a
source-pending primary citation can be inspected without a second lookup.
Use `artifacts <source_id>` for broader source-level acquisition planning,
especially when an operational crosswalk points to several primary sources.
Use `frontier` when the live obstruction is a `lean_linked` operational card
with open questions rather than a primary `source_pending` citation; it reports
the first next question, Lean target count, local text pointer, and compact
artifact/URL availability.
Use `lean <symbol>` for both direct Lean targets and dictionary-link symbols,
including `dictionary_open` or `staging_interface` navigation records.
Use `search <term>` for catalog text, Lean targets, dictionary-link symbols, and
`discharged_by` provenance strings. Search hits are navigation only: the
honesty-bearing fields remain the catalog `status` and `blocker` text.
Use `head-refs` to audit operational source prompts that mention repository
commits.  It classifies each commit anchor as `current`, `ancestor`,
`not-ancestor`, or `missing`, so stale prompt context can be refreshed without
treating historical anchors as catalog validation failures.

Para crear un paquete privado con los artefactos que ya existen en `YM_SOURCE_ROOT`:

```powershell
python scripts\source_db.py packet `
  --include-raw `
  --output source-packets\out\source-packet.zip
```

Sin `--include-raw`, el ZIP contiene únicamente catálogos, manifiestos, scripts y la base SQLite.

## Estados

1. `discovered`: documento o posible ubicación identificada.
2. `located`: páginas y ecuaciones localizadas.
3. `visual_confirmed`: la página fue inspeccionada visualmente.
4. `ocr_corrupted`: OCR útil para navegar, pero no para fijar fórmula exacta.
5. `source_pending`: el objetivo está definido, pero faltan datos exactos.
6. `source_extracted`: fórmula, hipótesis, cuantificadores y convenciones ya están transcritos con precisión.
7. `lean_linked`: el registro se enlaza con declaraciones Lean concretas.
8. `theorem_checked`: el consumidor Lean compila y pasa el oracle check.

## Promotion Checklist

Before promoting a citation to `source_extracted`, record all of these gates in
the catalog entry or an indexed handoff file:

- artifact hash and relative private-artifact path for every PDF, OCR text, or
  render used;
- visual page confirmation for formula-bearing pages, especially when OCR is
  corrupt or tag-localization is ambiguous;
- exact formula body, assumptions, quantifiers, constants, and source-local
  conventions;
- source-to-Lean dictionary fields needed by the named consumer;
- negative scope: the nearby theorem-looking claim or wrapper that must not be
  treated as discharged by this citation.

Before promoting a citation to `theorem_checked`, also record the named Lean consumer, the focused Lean command, and the oracle command that passed. A `visual_confirmed` or `source_extracted` entry is still not a proof until that consumer check exists.

## Política de contenido

No se deben subir a la repo pública PDFs completos ni OCR extensos de artículos protegidos. La repo guarda metadatos, fórmulas matemáticas, paráfrasis breves, localizadores y hashes. Los originales permanecen en un paquete privado reproducible.
