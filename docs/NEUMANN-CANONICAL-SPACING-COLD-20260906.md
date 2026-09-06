# Canonical Neumann spacing — fresh intermediate cold gate (2026-09-06)

CURRENT follow-up: same runtimea824030f7bc1 launched bounded internal-bond
HOT once20:05:18.902703UTC,PID17944,SOURCEc0174bbcb8f9b2b791cdb2c546206b468fd4e3cf.
Runner e15a6c288eb2702d7412039f74c0d8d79edb21d0,
SHA2566894d5bcfedebfda7427e6596883a7fa43cb45a025ad2347437fb484449428ac;
reader/tests87db895712a02943927690a3ed576d7509960d28.
Actual template-instantiation check passed0.4302728s/24997888observed RSS,
including10 synthetic rejections; that check is not compiler evidence.
Console /content/neumann-internal-bond-stencil-hot-v1-console.log.
Archive /content/neumann-internal-bond-stencil-hot-v1-evidence.tar.gz.
Do not rerun. The prepared wrap probe544218955 is not in this diagnostic.

FINAL: independently preserved COLD PASS, ledger1164, observed20:00UTC.
Focal8743jobs exit0/1645.627271009s; audit exit0/15.844011201s.
All16stages, exact3names/trio. Both redundant-ring warnings remain in the log.
Outer33830a24341b533cff91184a3e0967f6ce5f1e23654c6fbccf584bd7e23f485d;
innerf0166d3934ee455d70e618f9f8c33a0cc291c8efb99ee0217d47a71921128eb5;
independent reportff717adf491d3403d767a74e8ddaca70c6a0c39578bbe2ad84a61ab370bd0e50;
oleandbda0bf9590ece51553179d34eb947ceb5e543faba9333c11c938768da8020a2.
Preserved validation-evidence/neumann-canonical-spacing-cold-20260906.
Local bounded reader exit0/0.1612902s/16601088 observed peak RSS.
Runtimea824030f7bc1 remains retained for bounded R3 HOT, not another cold run.
Only the two certified headers retire PRE. The LIVE notes below are history.

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
