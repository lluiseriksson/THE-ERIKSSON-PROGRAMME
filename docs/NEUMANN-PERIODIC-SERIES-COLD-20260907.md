# Exact periodic series promotion: pending cold gate

Source checkpoint d16030e70abeee9eb77e28f5dc6a222ffdfd8200.
Runner/reader checkpoint57690fbda400c00e1ce7f2d45d9ecec603debfd9.
HOT parent archive7bf052a0e1117bb525e4633dc0fe07eee918ed1a660f208b22c2ef313e33209e
independently verified and preserved in ledger1208; not a cold seal.

Three source blobs hashed from git cat-file, never the CRLF worktree:
- NeumannPhysicalPeriodicSeries.lean:623b1de30820753db48f867259c667b0b22075b90784736896163995e54762b9
- NeumannPhysicalPeriodicSummability.lean:eb263b42a119777d162d1f83ec3c146feee284457d469f8f64c66f2154a3b71b
- NeumannPhysicalPeriodicSeriesAudit.lean:681a213bda0984596ddf52173d247e2a700cf8c52fee6c9e537bf307ae4e658b

Runner SHA2560ce5126790a5c10efdc5a7a3e98388c7f1f57f29f2c2df5f39f50edd3aea16d8.
Reader SHA256368b8c05d346571b04dbbd11447db203f4741b1247d9f0ad191b58698f69ec1f.
Use scripts/colab_neumann_physical_periodic_series_promoted_cold.ipynb
from its raw published commit. One launch only; CPU/highRAM>=40GiB, no GPU.
Fresh checkout, no project build restoration. Pinned Lean4.29.0-rc6 and
Mathlib07642720480157414db592fa85b626dafb71355b, portable preflight0/7,
text/import guards, then build both production modules and run shared audit.
Five exact names required; standard trio only. Stop first real child error.

Independent reader self-test: one positive/eight rejected, gate two/nine;
local measured0.112096s/17182720bytes observed RSS. Synthetic, not Lean evidence.
After result download archive, verify every log/record/contract/source pin and
both production outputs with reader and pinned helpers. Preserve before
disconnect/delete. No runtime left idle; no exploratory Actions.

PASS retires PRE only for these exact three modules after body equality check.
No root import is added by this leaf gate. No mixed coverage, uniform sum
budget, point-source equation, regional inverse, B0 or window15 claim.
20/41 and TermSource=0 stay fixed. Next analytic step remains mixed-family
coverage/owner transport and literal action, not a renamed arbitrary kernel.
