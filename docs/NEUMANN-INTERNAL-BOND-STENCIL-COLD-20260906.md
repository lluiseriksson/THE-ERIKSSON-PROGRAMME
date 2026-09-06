# Neumann internal-bond stencil — intermediate cold gate (2026-09-06)

Prepared, not executed. Source checkpoint81f35765ad50f8217bca20bc4530d99b3bf05103.
Exact HOT draft promotionc0174bbcb, preserved ledger1165: four actual
internal-bond adjoint/divergence identities, no free Green or boundary law.
Production and audit remain PRE-VALIDATION until fresh cold evidence.

Runner/reader checkpoint2b641e2ba98a78e2390252791c0a503778d33e67.
Runner SHA25615b6ec93051d138a1d2ee3197bb1cd4143ee18cdd3c542c901486800655ee43a.
Reader SHA2560c05cae2596a96c7fac5ff334da996b53ef153a06bdae4eaa68d368ffce55729.
Launcher checkpoint8111de7b896885565fdc6327e5c039b5acb7985e.
Launcher SHA256d7620dfeb9545a659e35f1b2390fcc9967fe12600ef8613b0998ec7ee3a405e6.

Single notebook cell, CPU/high-RAM >=40GiB, no GPU, same exact Lean/Mathlib.
No project-build restoration. Stop on first child error, preserve original
archive and independently verify before selective PRE retirement.
Package test exit0/0.4320049s/25071616 observed peak RSS: actual producer AST
agrees with independent reader, source blobs, four audit names, transport and
single notebook cell. Eight evidence corruptions plus four additional contract
corruptions rejected. Instrumental tests are not compiler evidence.

Notebook: scripts/colab_neumann_internal_bond_stencil_promoted_cold.ipynb.
Outer expected:
 /content/neumann-internal-bond-stencil-promoted-cold-v1-preservation-20260906.tar.gz
Local bounded preservation reader:
 scripts/preserve_neumann_internal_bond_stencil_cold.py
Arguments: --archive PATH --outer-sha256 HASH --destination NEW_PATH.
Never run Lean/Lake on Windows, duplicate the cell, or open exploratory CI.

After launch: prepare only the bounded rectangle wrap probe544218955;
it remains uncompiled and is not appended to the cold gate. This gate seals
the actual declared internal-bond operator, not a false nonperiodic rectangle
identification. The strict-fit/no-wrap producer remains explicit (R3).
20/41, TermSource=0, window15 compatible but not attained, Clay<0.1%.
