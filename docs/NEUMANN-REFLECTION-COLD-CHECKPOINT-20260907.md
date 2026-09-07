# Physical reflection cold promotion — active checkpoint

Source checkpoint: `84ceb5f2f466ab8f4e9dea175fd412c7bf63a21e`.
Runner/verifier checkpoint: `acdc7db315eb00690296c4fe1d55f3deda4f81cb`.
Launcher checkpoint: `eb879bdd2ebfffe427ad6f20fff57c9d4e396f69` (published).
Branch: `codex/cmp116-interacting-wilson-hessian`.

Seventeen production modules plus one audit. Bodies checked against diagnostic
checkpoint `0e652a6b170cd109163afbd5362134b8ce658d37`: 17/17 exact after only
import-path relocation and extraction of print-axiom lines; 52 unique audited
declarations. All eighteen textual guards passed. Local check 0.587372 s,
15376384 bytes observed RSS. Reader self-test: eight corruptions rejected,
0.1174609 s, 18341888 bytes observed RSS. These checks are not compiler evidence.

Colab tab 23, runtime f33828f71ae2, CPU/high RAM, lluiseriksson@gmail.com.
Single launch at 2026-09-07T03:25:33.709004+00:00, parent PID 48754.
No original notebook cell rerun. Fresh checkout directory:
`/content/hrpoly-neumann-physical-reflection-promoted-cold-v1`.
No project `.lake/build` restored from the retained diagnostic checkout.

Read-only continuation commands in the Colab terminal:

```sh
ps -p 48754 -o pid,stat,etime,args
tail -20 /content/launch-physical-reflection-cold-v1.log
tail -20 /content/neumann-physical-reflection-promoted-cold-v1-launch/physical_cold_graph.log
```

Do not restart on an observer timeout. The launcher preserves the child exit,
checks the cold archive independently and emits final status. Output archive:
`/content/neumann-physical-reflection-promoted-cold-v1-preservation-20260907.tar.gz`.
After completion download/preserve and independently verify hashes before
selective removal of production PRE-VALIDATION. Preserve first error on FAIL.
All earlier HOT/FAIL archives are durable in validation-evidence.

This is an intermediate cold brick, not terminal hRpoly. Regional image-series
equation and mixed-boundary seam remain open, along with the full-lattice
operator dictionary. Counters remain 20/41, TermSource=0, window15 not attained.
Unrelated dirty worktree files have not been touched.
