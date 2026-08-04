#!/bin/bash
# OS-R-0 bootstrap: ONE Colab cell (CPU/high-RAM runtime, never GPU).
# Paste into a fresh cell prefixed by %%bash, or run line-by-line.
# Runs the full stage ladder: judges (incl. judge_os_uniform, both modes),
# lane modules, core baseline, oracle, hashes.  Sentinels + logs land in
# /content/artefacts; read the logs, never trust exit banners alone.
#
# Expected at SHA c2723e7ec224191e00a9ab31284839816533ee86: judge_os_uniform
# 110/110 PASS in normal and optimized; core baseline 8480 jobs (docs/
# scripts-only commits since c7b870b05 — verify the count from the log
# tail, not from memory); oracle 3010 reports, triple standard axioms,
# 0 sorryAx.
#
# FIXED 2026-08-04 (second firing): the first committed version passed the
# SHORT SHA to the runner; stage 0 compares against `git rev-parse HEAD`
# (full 40 hex) and dies FATAL on the mismatch.  The SHA below is full.
# Also added: a terminal sentinel /content/OSR0_UNIT_DONE carrying the
# runner's real decimal exit code (atomic tmp+rename, one line), so a
# reader can distinguish absent / malformed / nonzero / zero.

set -e
SHA=c2723e7ec224191e00a9ab31284839816533ee86

# RAM guard (added after the SECOND firing died): the repo-wide oracle
# needs the high-RAM runtime; on the default 12 GB VM the kernel died by
# OOM mid-stage-4 at ~74 min and the VM was replaced, losing every
# artefact.  The runtime TYPE is a notebook setting the cell cannot fix,
# so fail FAST and loudly instead of 70 minutes in.
mem_kb=$(awk '/MemTotal/ {print $2}' /proc/meminfo)
echo "OSR0_MEMTOTAL_KB=$mem_kb"
if [ "$mem_kb" -lt 40000000 ] && [ "${OSR0_ALLOW_LOW_RAM:-0}" != "1" ]; then
  echo "FATAL: this is not a high-RAM runtime (MemTotal < 40 GB)."
  echo "Set the runtime type to High-RAM (Andra korningstyp) and rerun."
  exit 65
fi

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
# stage 4 repo-wide oracle, stage 5 hashes).  set -e is suspended around
# the runner so its real exit code reaches the sentinel even on failure.
set +e
python3 scripts/colab_dobrushin_d4_runner.py "$SHA"
rc=$?
set -e

# terminal sentinel: one line, the child's real decimal exit code,
# written atomically and validated before rename (CLAUDE.md protocol).
printf '%d\n' "$rc" > /content/OSR0_UNIT_DONE.writing
body="$(cat /content/OSR0_UNIT_DONE.writing)"
case "$body" in
  ''|*[!0-9-]*) echo "FATAL: malformed sentinel body '$body'"; exit 70 ;;
esac
mv /content/OSR0_UNIT_DONE.writing /content/OSR0_UNIT_DONE
echo "OSR0_UNIT_DONE=$rc"

# afterwards: read /content/artefacts/judge_os_uniform.*.log (110/110,
# count matches registration), the core log tail (job count), and the
# oracle log (reports count, axiom union read WITH continuations, -A2).
# Only then is OS-R fabrication licensed (charter section 5).
# Disconnect the runtime when the unit ends (owner rule 2026-08-01).
