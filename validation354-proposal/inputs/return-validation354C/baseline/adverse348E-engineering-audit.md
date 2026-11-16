# Separate static engineering audit: validation348E

Subject: `D:/Datos/the-eriksson-programme/autonomia/evidencia-348/validation348E-preparation`, frozen outer manifest raw SHA256 `bac4f1ccef8f7461637fa79fdd3217b811eef7b556fe64f2cacf96ecd1489159`.

**Verdict: HOLD_FOR_REPAIR. One blocking engineering finding (B1) prevents approval of this exact package as execution-ready under the repository sentinel rule.** The narrow TeX classifier repair itself is correct by static inspection. No candidate Python was executed, imported, syntax-checked or tested. Current normal/-O regressions and actual-return validation remain pending. This is not a scientific/PDF assessment and does not modify or revisit review348D.

## B1 — direct publication of exit sentinels in the notebook wrapper

Location: `03-preflight.py`, lines 28–29, function `observed_child`; the same bytes are in the corresponding notebook code cell. The helper is used for the current preflight caller and both actual-return calls.

The final `.exit` path is opened directly with exclusive mode and receives the decimal exit in one ordinary write. There is no temporary-file publication, fsync, readback validation, or final atomic rename. An interrupted write can therefore leave the public sentinel empty or incomplete. The row correctly records the waited child's return code in memory, and current success checks do not infer success solely from sentinel existence; I am not claiming an observed false PASS. Nevertheless, this is a concrete violation of the active Operational Governance Charter's explicit exit-sentinel protocol, and exported `.exit` files are part of the promised raw evidence.

Required repair: write the actual closed child's decimal exit and one newline to a fresh temporary path, flush/fsync and close it, explicitly validate nonempty integer syntax and equality to the observed exit, then publish atomically while preserving the package's no-overwrite rule. Validate the published bytes before adding them to the receipt. Retain interruptions/failures rather than emitting a successful observation. Update the standalone cell, notebook and hashes in a new immutable package; do not amend the reviewed348E snapshot or any old failure. Add narrowly targeted failure/interruption/duplicate-destination regression coverage for this wrapper on the sanctioned Linux plane. No PDF or production rebuild is needed.

The inner `runtime/run_preflight348E.py` already uses a temporary exit file, flush/fsync, explicit readback and rename. B1 concerns the outer notebook helper, not that inner preflight implementation.

## Findings that support the narrow repair

### Actual previous failure and classifier delta

The retained348D UI capture records both actual normal and explicit `-O` invocations returning exit1 with `ValueError: Exact native TeX argv`. The companion environment capture reports optimize0/1 and no PYTHONOPTIMIZE override. These are retained UI observations, not a recovered complete native failure archive. They must remain failures.

The read-only old/new validator diff contains the new named classifier, its insertion into full validation, removal of the broad prefix predicate, and the version label change. The old `startswith('tex-')` condition included `tex-version`; the actual production report records exactly `['pdflatex','--version']` for it. The new classifier first checks all27 command names in order, then checks that precise version argv separately and exactly four compilation names against the unchanged no-shell-escape argv and deterministic TeX argument. It does not admit an unknown TeX-labelled command because the full name/order comparison precedes classification. `check_report` still verifies native exit types/values and timeouts. Full validation calls both report checking and the new classifier, so direct classifier tests do not accidentally replace exit validation.

The actual report fixture matches the original production archive member byte for byte. The five new regression cases accept the real27-command sequence as data and reject changed version argv, a missing compile command, enabled shell escape, and a changed final compile argument. The original63 cases remain, giving expected totals6 accepts/62 rejects over68 distinct cases. This is a static expectation, not a passed run. The preflight requires those counts, distinct labels, matching per-case decisions, both semantic modes, raw receipts and actual child exits. No acceptance branch in the inspected current scripts relies on Python `assert`.

### Current and historical preflight separation

Current preflight uses348E validator/tests/checker and the actual-report fixture, binds their bytes through the current manifest, requires the exact fresh348E root and an unmodified optimize0 launcher, and explicitly launches both normal and `-O` children. `ready` starts false and only becomes true after both accepted outputs; exceptions retain the report through `finally`.

Historical production receipts are extracted into a separate `production-preflight` directory and checked through the pinned original348D checker loaded under a distinct module name. Its original5/58,63-case semantics and recorded `/content/ui-production348D` test argv remain intact. Only the old checker function is invoked; its guarded main is not run. The old builder, launcher, marker and old tests are not executed by the new caller. All eight historical runtime payloads match the unchanged historical manifest. Thus old synthetic evidence is not silently promoted into new68-case evidence, and neither synthetic preflight is a substitute for actual full-return validation.

### Caller and bindings

The caller enforces `/content/ui-validation348E`, explicit optimize0/1 with no PYTHONOPTIMIZE override, fresh mode-specific outputs, and exact original archive hash and length. Its own bytes are checked against the current runner manifest, whose bytes are pinned by the materializer. The validator, source inventory, current preflight checker, old checker and old runner manifest have explicit pins. The current preflight is checked before accepting the actual input.

The outer archive must contain exactly ten regular unencrypted members under fixed names, with a size bound. The seven historical preflight members are likewise bounded and fixed. The full validator retains the original source44 universe, raw member hashes, matching build PDFs, native exit/log inventory, deterministic metadata argument, page inventory, source binding and native retained-output checks. It returns a scoped structural result only after those checks. The caller writes failure text on exceptions within its protected operation; output directories and files are exclusive. It does not run a builder or renderer.

The current summary starts `accepted=False`, requires successful child observations in both modes, compares returned structural identities, and explicitly requires the known original PDF hash/length/pages before setting true. A nonzero return from the first completed child does not prevent attempting the second. An allocation/interruption exception exits before that final summary, while the helper is intended to retain its own failed observation; missing summary is not success. B1 must still be fixed before relying on its sentinel artifacts.

### Materialization, chunks, assembly and export

The notebook contains seven unexecuted code cells, all exactly equal to the supplied separate cell files, with null execution counts and empty outputs. The first cell requires a real operator-supplied runtime hostname; the blank value is a deliberate stopping placeholder. It pins the current runner manifest and verifies17 embedded payloads, with contained paths, exclusive writes and disk readback. The payload JSON was decoded as data for this audit; no Python code was evaluated.

The input cell is bounded to one indexed base64 chunk, checks the indexed raw length/hash, exclusively writes it, reads it back and emits a timestamped receipt. Assembly rereads the28 sequential chunks and their hostname/hash-bound receipts, verifies the aggregate raw input before an exclusive write, and verifies disk readback. I independently decoded and reassembled the frozen chunks in memory as bytes; they reproduce the unchanged original5429697-byte UI archive hash. This is transport verification, not execution of the candidate assembler.

The exporter selects available receipt/log/result/failure files, enforces a bounded total and unique member names, writes a fresh ZIP, then reopens it and checks inventory and member hashes. It can export partial failure evidence and makes no success, browser-download or runtime-closure inference. It does not include redundant production ZIPs. I found no additional execution-ready blocker in the inspected export logic. Actual export bytes must still be verified by the parent after Linux execution.

## Independent static evidence obtained

- All59 outer manifest entries matched their raw byte lengths and SHA256 digests; the assigned outer manifest hash matched.
- All16 current runner entries and all8 historical entries matched their manifests.
- All7 notebook code cells matched the separate sources and were unexecuted.
- All17 embedded materialization payloads decoded to exact runtime files.
- All28 base64 transport files were canonical encodings of their declared raw chunks; ordered reassembly gave5429697 bytes and SHA256 `b74ab3e6e1d349aafe5ed42d984270e0ae1ee86ac158a1d9738dc6274f1b6e4b`.
- That hash matches the original `actual-production348D/ui-return348D.zip` read directly. The actual report member matches the fixture at12194 bytes, SHA256 `61cbed4954ecdfb67b322cc7dcf791720c9470029981743a0c9286ea2c769deb`.
- The nested PDF was hashed as uninterpreted bytes only:345832 bytes, SHA256 `9f5d88b88321ca9ddc2afd284861a217cde0a37057362c1962a8cf988c42b29a`. No page was reopened, rendered or reassessed.

These observations are recorded in `static-inspection.json` and `transport-binding-inspection.json`. They do not certify runtime behavior, regression outcomes or a successful actual return.

## Scope and disposition

Only B1 is an identified blocking defect in this static engineering audit. Additional residual limits are retained: the external old UI failure capture is not the complete raw failure archive; tests cover predicates and this specific field regression rather than every archive branch; CPU/high-RAM selection, exclusive runtime ownership, launch/closure and absence from Manage sessions require separate actual UI evidence; and neither this audit nor a future structural success establishes mathematics, a grade, publication permission or collection acceptance.

The next permitted step is a distinct immutable repair of B1, separately checked against this finding, followed by actual Linux normal/-O regressions and full actual-return validation. This report does not authorize treating any expected result as observed. The original348D production, old failures, this348E preparation snapshot and the prior scientific review remain immutable.

Identity/context: OpenAI/Codex assistant in a separate audit role from the348E fabricator. This same evaluator previously performed review348D; that prior scientific work was not reopened. Shared provider/workspace lineage exists, and exact backend/model/effort and technical/statistical independence are not attested. No inbound coordination arrived during this audit. Local activity was limited to file/JSON/base64/ZIP-byte reads, hashing, read-only diff, and writing this report. No candidate import, compiler, tests, mathematical execution, PDF production, Git mutation, service, runtime or publication operation occurred.
