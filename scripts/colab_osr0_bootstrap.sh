#!/bin/bash
# OS-R-0 bootstrap: ONE Colab cell (CPU/high-RAM runtime, never GPU).
# Paste into a fresh cell prefixed by %%bash, or run line-by-line.
# Runs the full stage ladder: judges (incl. judge_os_uniform, both modes),
# lane modules, core baseline, oracle, hashes.  Sentinels + logs land in
# /content/artefacts; read the logs, never trust exit banners alone.
#
# Expected at SHA c2723e7ec: judge_os_uniform 110/110 PASS in normal and
# optimized; core baseline 8480 jobs (docs/scripts-only commits since
# c7b870b05 — verify the count from the log tail, not from memory);
# oracle 3010 reports, triple standard axioms, 0 sorryAx.

set -e
SHA=c2723e7ec

rm -rf /content/eriksson
cd /content
git clone -b d3-closure --single-branch \
  https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git eriksson
cd /content/eriksson
git checkout "$SHA"

# toolchain
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
source "$HOME/.elan/env"

# mathlib cache (NOTE: cache get does NOT cover the YangMills tree; the
# core build after cache is minutes, not hours)
lake exe cache get || true

# the full pre-registered ladder (stage 0 env, stage 1 certifiers incl.
# judge_os_uniform normal+optimized, stage 2 lane modules, stage 3 core,
# stage 4 repo-wide oracle, stage 5 hashes)
python3 scripts/colab_dobrushin_d4_runner.py "$SHA"

# afterwards: read /content/artefacts/judge_os_uniform.*.log (110/110,
# count matches registration), the core log tail (job count), and the
# oracle log (reports count, axiom union read WITH continuations, -A2).
# Only then is OS-R fabrication licensed (charter section 5).
# Disconnect the runtime when the unit ends (owner rule 2026-08-01).
