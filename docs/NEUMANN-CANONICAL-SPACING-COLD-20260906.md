# Canonical Neumann spacing — fresh intermediate cold gate (2026-09-06)

Status: LIVE, one execution started2026-09-06T19:30:22.418089UTC.
Hash gate PASS; launcherPID1139. Colab CPU/highRAM50.99GB, account
lluiseriksson@gmail.com. Notebook vehicle6eb506f130c1bd3d42d891879c78749502dfac24,
browser tab9/cellJj0kgx_GMieQ. No mathematical cold verdict yet.
Do not rerun the cell or close this active tab before evidence preservation.
Runtime hostnamea824030f7bc1. One bootstrap check at19:35:06UTC showed
lake_update exit0, exact Mathlib pin, cache_get exit0 and entry into
canonical_spacing_focal. Only official Mathlib cache8142 was downloaded;
the project graph is compiling fresh. No FAIL or final verdict observed.
Next coarse observation around20:00UTC, not a minute-by-minute polling loop.
R3 HOT templates/checks are checkpointedd65d65c9ca8631dcb32a93ba540cf6076dcfd381.
SOURCE_CHECKPOINT=dd9354a87d2e9d60dac69aa79f287b53e45ba207
Runner/reader checkpoint=e2693781db75058bd69d74fa659b17da2f89d6f0
Runner SHA256=dc92529f0d7f10a076c939f32462872cd3a362abc0c057b299e1386a35b06c9f
Reader SHA256=50ed7d38dc3695a48eb1e709f0b10f5ac14a9ec3c60f526f1c89c7ae4805ca94
Launcher checkpoint=339d5a2e7a353a221c7d6a203d6ff70ef0e3c1ea
Launcher SHA256=c183117cf3277f8e4ff88a75bc0e86ac73af0267c8a4920baef4978a3bcdbbc6

Exact-body promotion from HOT852d3b82e preserved in ledger1163.
Three declarations: terminal spacing one, literal counting coefficient,
combined counting-mass coefficient. No boundary inverse or uniform B0.
No project build restoration. Official toolchain4.29.0-rc6 and Mathlib
07642720480157414db592fa85b626dafb71355b remain pinned.
The actual producer AST and independent reader agree on the source,
two source blob hashes, three audit names and exact queue. Synthetic tests
reject8 evidence corruptions and4 additional contract corruptions; package
check exit0/0.554989s/25096192 observed RSS. Not compiler evidence.

Open only scripts/colab_neumann_canonical_spacing_promoted_cold.ipynb at
its published raw Git SHA. One cell, CPU/high-RAM >=40GiB, no GPU.
Do not rerun the cell. Check hash gate, actual execution start and PID.
Expected outer:
 /content/neumann-canonical-spacing-promoted-cold-v1-preservation-20260906.tar.gz
Independent local reader:
 scripts/preserve_neumann_canonical_spacing_cold.py
Use --archive, --outer-sha256 and a new --destination; bounded local reader
only, never Lean/Lake on Windows. Preserve original archive before selective
PRE retirement. Known HOT redundant-ring warnings are not suppressed.

After launch prepare only the bounded R3 finite-stencil diagnostic on sealed
dependencies: bond restriction/zero-extension adjoint, Neumann derivative
factorization, then existing active-region divergence applied to the
zero-extended INTERNAL derivative. Do not identify it with Dirichlet.
See docs/NEUMANN-INTEGER-TO-PHYSICAL-NEXT-20260906.md.
20/41, TermSource=0, window15 compatible but not attained.

Bounded next HOT diagnostic prepared (NOT RUN):
sourcec0174bbcb8f9b2b791cdb2c546206b468fd4e3cf,
tmp/NeumannInternalBondStencilDraft.lean and Mathlib-only Repro.
Four named identities: counting bond adjoint, actual derivative factorization,
adjoint with INTERNAL bond extension, literal finite divergence. The existing
Dirichlet divergence is consumed only after this extension, never identified
with Neumann. No positivity, nonempty-region, or boundary identity is assumed.
Text/import guards passed0.1416958s/13991936RSS. Templates under
tmp/*neumann_internal_bond_stencil_hot_template.py deliberately leave four
parent-cold pins and the reader's runner hash unset. Synthetic template test
passed1 fixture, rejected10 corruptions, preserved1 failure;0.404482s/
23408640RSS. It checks actual Git-blob imports and all four audit names.
No compiler evidence for this draft. Fill pins only after the current cold
archive is independently preserved; then reuse the SAME runtime if available.
Never reset or re-clone it merely to debug these four identities.

Static audit while this cold graph runs identified an additional explicit
acceptance gate R1b/R3 in NEUMANN-INTEGER-TO-PHYSICAL-NEXT-20260906.md:
the Eq243/246 source is xi^(-d)-normalized while the finite counting kernel
operator probes an unscaled delta. The actual inverse proof must show which
RHS it solves and transport the xi^d factor explicitly. This is not a newly
proved no-go, does not alter the current spacing statements or source SHA,
and must not be hidden inside the already distinct Q-adjoint mass convention.
