#!/usr/bin/env bash
# Isolated elaboration of S-2a, with an ABORTIVE preflight.
#
# Contract (owner, this round):
#   * preflight aborts on HEAD or sha256 mismatch -- it never merely prints;
#   * ONLY the S-2a module is elaborated, not the whole library;
#   * the log is emitted in full: no tail, no grep, no summary.
#
# EXPECT_HEAD is passed in by the caller so that the URL this script is fetched
# from and the commit it verifies are the same object.
set -u
export PATH="$HOME/.elan/bin:$PATH"

REPO=/content/repo
BRANCH=claude/congruence-spectrum
MODULE=YangMills/OS/ProjectiveDiameterMonotone.lean
EXPECT_S2A=21c43f6abf1644e5176361954f43fa3e14f7636c7cdbbf5d02a0a8b27800426b
EXPECT_HEAD="${EXPECT_HEAD:-}"

if [ -z "$EXPECT_HEAD" ]; then echo "PREFLIGHT ABORT: EXPECT_HEAD not supplied"; exit 1; fi

if [ -d "$REPO/.git" ]; then
  cd "$REPO" || exit 1
  git fetch --quiet origin "$BRANCH" || { echo "PREFLIGHT ABORT: fetch failed"; exit 1; }
  git checkout --quiet -B "$BRANCH" "origin/$BRANCH" || { echo "PREFLIGHT ABORT: checkout failed"; exit 1; }
else
  git clone --quiet --branch "$BRANCH" --single-branch \
    https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git "$REPO" \
    || { echo "PREFLIGHT ABORT: clone failed"; exit 1; }
  cd "$REPO" || exit 1
fi

GOT_HEAD=$(git rev-parse HEAD)
GOT_S2A=$(sha256sum "$MODULE" | cut -d' ' -f1)
echo "HEAD $GOT_HEAD"
echo "S2A  $GOT_S2A"
if [ "$GOT_HEAD" != "$EXPECT_HEAD" ]; then echo "PREFLIGHT ABORT: HEAD mismatch"; exit 1; fi
if [ "$GOT_S2A" != "$EXPECT_S2A" ]; then echo "PREFLIGHT ABORT: module sha256 mismatch"; exit 1; fi
echo "PREFLIGHT OK"

if ! command -v lake >/dev/null 2>&1; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none >/dev/null 2>&1
  export PATH="$HOME/.elan/bin:$PATH"
fi
lake --version || { echo "ABORT: no lake"; exit 1; }

lake exe cache get > /content/cache.log 2>&1
echo "cache get exit $?"

echo "=== STEP 1: ISOLATED ELABORATION OF S-2a ==="
lake env lean "$MODULE" > /content/s2a.log 2>&1
echo "S2A EXIT $?"
echo "--- BEGIN s2a.log (full: no tail, no grep) ---"
cat /content/s2a.log
echo "--- END s2a.log ---"

# Step 2 decides one thing only, and it is a diagnosis and not a fix: whether the
# failure is an absent import or a genuine error in the mathematics.  Same body,
# same proofs, the whole of Mathlib in scope.
echo "=== STEP 2: SAME BODY, import Mathlib ==="
sed -e 's|^import Mathlib.Data.Matrix.Basic$|import Mathlib|' \
    -e '/^import Mathlib.Algebra.Order.BigOperators.Ring.Finset$/d' \
    "$MODULE" > _probe_full.lean
grep -n '^import' _probe_full.lean
lake env lean _probe_full.lean > /content/probe.log 2>&1
echo "PROBE EXIT $?"
echo "--- BEGIN probe.log (full) ---"
cat /content/probe.log
echo "--- END probe.log ---"
