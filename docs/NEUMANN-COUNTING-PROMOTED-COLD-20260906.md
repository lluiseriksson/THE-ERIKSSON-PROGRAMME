# Counting reflection and retained mass — promoted cold gate

Prepared before connection. Not yet compiler-verified at this checkpoint.
Prior goal turn made progress: both diagnostic artifacts independently verified,
preserved and published, then exact source promotion. Counters remain20/41,
TermSource0, window15 unattained. R1/R2/R3/R4 are still the physical boundary.

## Exact object

- SOURCE `9b73a5fe37d1e5e3c8589af211c46708a9d0a7bb`.
- Four files: `NeumannGeneratedCountingMassReflection(+Audit)` and
  `NeumannRetainedCountingMassDictionary(+Audit)` under `YangMills/RG`.
- Reflection focal → three-name audit → retained dictionary focal → two-name audit.
- Two production `.olean` outputs; audits run directly, no audit `.olean` claim.
- No root/repo-wide claim. No restored project build graph, one fresh checkout.
- CPU/highRAM≥40GiB/noGPU, Colab account lluiseriksson@gmail.com.

Binary Git-blob SHA256 references, not CRLF worktree hashes:

| file | SHA256 |
|---|---|
| NeumannGeneratedCountingMassReflection.lean | e97f83ada28c0300d80119b9d1b289001975148caf539805ca09cbbaa9666ae6 |
| NeumannGeneratedCountingMassReflectionAudit.lean | 5c0769526ec970014d322ac2c13fb3f992fb16287516c7733d516735e572bc4f |
| NeumannRetainedCountingMassDictionary.lean | aee40a157a0538c87ccd0f1ab157919d9b2ccfc94efd453de4d844b65bf875d9 |
| NeumannRetainedCountingMassDictionaryAudit.lean | 592092738e1b3f8c7039e528350c4a5efeece55a483ae37ca24479d78bcc7776 |

## Transport and instruments

Runner/verifier commit `2ef47fc11740a21c4c495fc8d80e0216fdce3887`:
runner `87aafa61ce1824a5b8fc4acf4cd107944b52e9531d2fb37bebaa3dde99d9033f`,
verifier `9decd5ede386cf72c30c6a1909e545f852a68e8fad4801ba48674adbe0caf5c5`.
Launcher commit `b8f85c9dc28920f5c0b0552f1c8a45a86baa0e62`,
SHA256 `6f124ac7c43e7f3fa247123db0420b2c903c7e9161ac6a06fcf670d3ef5d69d9`.
Notebook `scripts/colab_neumann_counting_promoted_cold.ipynb`: one code cell,
no outputs, source/revision unique, launcher hash checked before execution.

The launcher runs portable preflight and verifier self-tests, then the cold
graph, then independently verifies the inner archive. Real child codes,
durations, full logs and their hashes are preserved. Parent diagnostics are
recorded separately in the contract (ledger1128/1129); they cannot replace the
promoted cold outputs. Failure stops the queue and preserves the first error.

`scripts/preserve_verify_neumann_counting_promoted_cold.py` checks the outer
archive, launcher/helper pins, exact three launch commands, final status,
inner graph/axioms/output hashes, then writes the durable destination. No
overwrite and no extraction before verification. Actual PASS not exercised yet.

Prelaunch instrument checks: exit0/0.1770168s,18309120 observed peak bytes,
single Windows process under30s/512MiB watchdog, no Lean/network/pool. Exact
four-file/five-name/queue consistency, notebook/launcher/preserver consistency,
two valid+nine forbidden axiom fixtures, old six and new eight negative metadata
fixtures. Synthetic fixture PASS is not mathematical evidence.

## Runtime lifecycle

Single launch confirmed at `2026-09-06T06:23:49.945876+00:00`, after the
launcher hash gate: CPU/highRAM50.99028778076172GiB/noGPU, visible account
lluiseriksson@gmail.com. Host `a7df6ab4f6f3`, launcher PID11958, parent11935.
Notebook vehicle commit `e674202c8ff128292a7ca4b096e6ada2927930dc`.
The ordinary own-GitHub-notebook warning was confirmed once; the evidence
clock starts at the printed hash gate, not the preceding click. Initial
toolchain/checkout/source-text/import gates passed; last observed stage
at06:30UTC is reflection_focal, with launcherPID11958 still live (elapsed06:23)
and UI execution active. Mathlib cache_get exit0/7.331s,8142 files decompressed.
No final verdict observed. Keep the one live tab, do not reexecute.

An additional preserver negative test rejected the actual earlier v2 diagnostic
archive as the wrong cold object (`OUTER_FILES`) before writing anything.
Complete local instrument check exit0/0.3474336s,21856256observed peak bytes.
This is instrument evidence only. Current cold source/runner were unchanged.

Expected console `/content/neumann-counting-promoted-cold-v1-console.log`.
Expected launch `/content/neumann-counting-promoted-cold-v1-launch`.
Expected outer `/content/neumann-counting-promoted-cold-v1-preservation-20260906.tar.gz`.
Expected inner `/content/hrpoly-neumann-counting-promoted-cold-v1-evidence.tar.gz`.
Execute once. Inspect existing handle after observer failure, never restart on
timeout alone. Prior physical prerequisites23–31min: read near that threshold,
not each minute. Preserve/verify final evidence, then disconnect/delete runtime.
Only then selectively retire promoted PRE-VALIDATION, with proofs unchanged.
