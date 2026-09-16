# Mixed physical convergence HOT diagnostic prepared, not running

The active FULL diagnostic remains PID18097 in Colab tab55. Do not overlap
its compiler or relaunch it. At the last read, its prerequisite build was
advancing through CMP99 source-cell modules, around 930 seconds into build.

Next HOT source `bee3c451b41b5da2a1d876d7ad3f0de27a17bdee`;
draft SHA256 `b2a338a4b7f682dcfb68dc616e9f3a4e8749239fd9021c77e3847fa0737c8da8`.
Runner commit `31b2eff581900228ea0226675d5a4305db11bbce`;
`scripts/colab_neumann_physical_mixed_summability_hot.py` SHA256
`43a7113220eb3cdb6706793090a4c27e92b8be6cf12d9465bf24d402935c1fd2`.
Independent reader `scripts/verify_neumann_physical_mixed_summability_hot.py`.
It checks exact file set, manifest, runner/source hashes, both commands,
child exits, timings and all three exact axiom declarations; never cold seal.
Synthetic test: one accepted/eight rejected, 0.1788564s/19922944 peak RSS.
No local compiler, no actual diagnostic result from these synthetic tests.

After FULL finishes: preserve/verify its archive first, then create
`/content/full-flag-evidence-preserved.ok` as operational acknowledgement.
Only then launch this runner once, with stdout OUTSIDE its evidence folder,
e.g. `/content/mixed-summability-hot-launch.log`. Its receipt and no-active-
compiler checks prevent accidental overlap. ROOT remains the retained FULL
checkout at f0c58431d20042ced9177632409e9f9bcbe79692; only the pinned scratch
draft is downloaded from the later source. No checkout of a running tree.

Output `/content/neumann-physical-mixed-summability-hot-v1.tar.gz`.
Download automatically, compare hashes, then use the independent reader.
This is only convergence of the literal (2.46) full Green on the SAME mixed
index. No uniform norm budget, operator interchange or physical inverse.
20/41 and TermSource0 unchanged.
