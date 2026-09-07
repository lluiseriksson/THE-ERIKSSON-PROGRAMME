# Half-cell phase diagnostic preserved PASS checkpoint

2026-09-07: original archive downloaded and independently verified PASS.
Archive SHA256 5e0acff780e5829778d62e0d1e13df3d4ac75c556138800120d3361fd40dd992.
Report SHA256 a2161e6845eb72020735a639b687d7383975772f61f2daf942e1a57571e7fbc9.
Evidence: validation-evidence/neumann-half-cell-phase-diagnostic-v1-20260907.
Runtime e2e36fff9f96 disconnected and deleted after preservation; reconnect-only
UI confirmed around 00:07 UTC. No rerun. See ledger Addendum 1182.

Source7320d1bab92f0bcb18d8072dd0d2fa13b1aea204;
runner0505a1567cd48a5a9838e50103be80108324d171;
notebook/reader12f3612d5563601488f917ba33a9e035a6b9a35e.
Runner SHA256 ecd76d0c05609aa45a4dc1c69e33ae9fa0dfb8600283760464c8d547697a42b8.

One launch confirmed 2026-09-06T23:58:51.675083Z, PID8694, CPU/high RAM50.99GB,
visible account lluiseriksson@gmail.com. Security dialog confirmed once.
No second cell launch. IAB tab16; source notebook URL:
https://colab.research.google.com/github/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/12f3612d5563601488f917ba33a9e035a6b9a35e/scripts/colab_neumann_half_cell_phase_diagnostic.ipynb

Runtime log /content/launch-neumann-half-cell-phase-v1.log.
Streaming child logs /content/hrpoly-neumann-half-cell-phase-diagnostic-v1-evidence/.
Original archive /content/hrpoly-neumann-half-cell-phase-diagnostic-v1-evidence.tar.gz.
Check existing process/logs; never reexecute because an observer times out.
Queue: bootstrap/cache, scratch path, phase_repro, physical prerequisites,
phase_physical, clean_after. Mathematical stages timeout120s. First error
stops queue. Completed PASS; 19 records exit 0, two exact oracle blocks.

PASS reader: scripts/verify_neumann_half_cell_phase_diagnostic.py --archive
<downloaded-original> --sha256 <actual-Colab-hash> --destination <fresh-folder>.
Its synthetic test accepted1/rejected14; these are NOT compiler evidence.
On FAIL preserve exact original first error separately; do not force it
through the PASS reader or call it a seal.

Both Lean inputs remain PRE. This proves at most finite-average phase,
not Green covariance, regional inverse, physical B0 or window15.
Counters20/41,TermSource0 unchanged. Parent cold/HOT archives already
preserved in ledger1180/1181; the previous runtime was deleted.
