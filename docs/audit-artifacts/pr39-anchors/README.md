# PR #39 literal-anchor adversarial evidence

This directory preserves the synthetic checkpoint and four rejected runs used to audit PR #39's literal trust anchors.
Synthetic A tree: `0f5a38a4a81bf069ff20f50e395f5e380c1b5000`.
Synthetic B tree: `50262878f0d784fb03d316b0f0c561e7707bc556`.
Synthetic A commit: `7fb53aa7ebd94fdb9aeb9a949e4e8780d92c9134`; parent `29a3f203f2a4323af18ef43a4eddb83c3b500c16`; subject `synthetic A: neutralize decisive trace acceptance condition`; author and committer `Independent PR39 audit fixture <pr39-audit-fixture@local.invalid>`; date `2026-08-02T13:36:27+02:00`.
Synthetic B commit: `d64ebd05c1b4b9540f49eb8a980224421d6879af`; parent `7fb53aa7ebd94fdb9aeb9a949e4e8780d92c9134`; subject `synthetic B: self-consistent evidence for neutralized checkpoint`; author and committer `Independent PR39 audit fixture <pr39-audit-fixture@local.invalid>`; date `2026-08-02T13:39:05+02:00`.
Runs 01 and 02, from `synthetic-repo/`: `python scripts/verify_pr39_instrumental_bundle.py --head d64ebd05c1b4b9540f49eb8a980224421d6879af`.
Runs 03 and 04, from `synthetic-repo/`: `python -O scripts/verify_pr39_instrumental_bundle.py --head d64ebd05c1b4b9540f49eb8a980224421d6879af`.
The mutated certifier contains `mutation is None or hd_diagonal.trace() == expected_hd_trace`, neutralizing the real-input decision while retaining mutation checks.
`PHASE1-FREEZE.txt` records the frozen object graph; `run-*.json` records the four causal rejections at literal certificate anchor check 17.
The 69,674,078-byte Git bundle and synthetic `.git` database are deliberately excluded; the auditable 72 KB payload is retained here.
