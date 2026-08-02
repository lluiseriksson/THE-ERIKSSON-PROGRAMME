#!/usr/bin/env bash
# Bootstrap a Colab Linux runtime for the S block.  CPU, never GPU.
#
# Owner's rule of 2026-08-01: Colab is the sanctioned compilation plane.  This
# script reads no token, writes no token, and pushes nothing.  It leaves a
# clone at /content/eriksson and a toolchain, so that every later cell is one
# short line.
#
# It is deliberately NOISY about which step it is on, because the failure it is
# most likely to hit -- a cache that does not match the pin -- looks like a slow
# build rather than an error.
#
# Usage (one Colab cell):
#   !git clone -q -b <branch> https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME /content/eriksson && bash /content/eriksson/scripts/colab_bootstrap.sh
set -u

REPO=/content/eriksson
PIN_TOOLCHAIN="leanprover/lean4:v4.29.0-rc6"
PIN_MATHLIB="07642720480157414db592fa85b626dafb71355b"

echo "=============================================================="
echo "stage A  environment, checked BEFORE anything expensive starts"
echo "=============================================================="
nvidia-smi >/dev/null 2>&1 && echo "  NOTE: a GPU is attached.  This lane never needs one." || echo "  no GPU attached (correct)"
echo "  cores : $(nproc)"
echo "  memory: $(free -g | awk '/^Mem:/{print $2}') GiB"
cd "$REPO" || { echo "FATAL: no clone at $REPO"; exit 2; }
echo "  repo SHA  : $(git rev-parse HEAD)"
echo "  branch    : $(git rev-parse --abbrev-ref HEAD)"
TC=$(cat lean-toolchain)
echo "  toolchain : $TC"
if [ "$TC" != "$PIN_TOOLCHAIN" ]; then
  echo "FATAL: toolchain $TC is not the pin $PIN_TOOLCHAIN"; exit 2
fi
if ! grep -q "$PIN_MATHLIB" lake-manifest.json; then
  echo "FATAL: Mathlib pin $PIN_MATHLIB absent from lake-manifest.json"; exit 2
fi
echo "  mathlib pin found"

echo
echo "=============================================================="
echo "stage B  elan and the pinned toolchain"
echo "=============================================================="
if [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -o /tmp/elan-init.sh || { echo "FATAL: could not fetch elan-init"; exit 2; }
  sh /tmp/elan-init.sh -y --default-toolchain "$PIN_TOOLCHAIN" >/tmp/elan.log 2>&1
  echo "  elan install exit: $?"
  tail -3 /tmp/elan.log
else
  echo "  elan already present"
fi
export PATH="$HOME/.elan/bin:$PATH"
echo "  lake  : $(command -v lake)"
echo "  lean  : $(lean --version 2>&1 | head -1)"

echo
echo "=============================================================="
echo "stage C  Mathlib oleans from cache (NOT a build of Mathlib)"
echo "=============================================================="
cd "$REPO"
lake exe cache get > /tmp/cache.log 2>&1
echo "  cache get exit: $?"
tail -5 /tmp/cache.log

echo
echo "=============================================================="
echo "stage D  the lane module"
echo "=============================================================="
lake build YangMills.OS.SpatialOS 2>&1 | tail -80
echo
echo "lane build exit: ${PIPESTATUS[0]}"
echo
echo "Every later cell can now be one line, for example:"
echo "  !cd /content/eriksson && git fetch -q origin <branch> && git reset -q --hard FETCH_HEAD && PATH=\$HOME/.elan/bin:\$PATH lake build YangMills.OS.SpatialOS 2>&1 | tail -60"
