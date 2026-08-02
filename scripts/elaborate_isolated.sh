#!/usr/bin/env bash
# Elaborate ONE module in isolation and print its log in full.
#
# Generalised from scripts/s2a_isolated.sh once the same need arose for a second
# module.  Two modules are never debugged in the same elaboration: a shared run
# mixes their diagnostics and invites reading one module's cascade as the other's
# cause.
#
# Required in the environment:
#   EXPECT_HEAD   commit this script was fetched from, verified before anything runs
#   MODULE        path of the single module to elaborate
#   EXPECT_SHA    sha256 of that module
set -u
export PATH="$HOME/.elan/bin:$PATH"

REPO=/content/repo
BRANCH=claude/congruence-spectrum
EXPECT_HEAD="${EXPECT_HEAD:-}"
MODULE="${MODULE:-}"
EXPECT_SHA="${EXPECT_SHA:-}"

if [ -z "$EXPECT_HEAD" ]; then echo "PREFLIGHT ABORT: EXPECT_HEAD not supplied"; exit 1; fi
if [ -z "$MODULE" ];      then echo "PREFLIGHT ABORT: MODULE not supplied"; exit 1; fi
if [ -z "$EXPECT_SHA" ];  then echo "PREFLIGHT ABORT: EXPECT_SHA not supplied"; exit 1; fi

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
if [ ! -f "$MODULE" ]; then echo "PREFLIGHT ABORT: module not present"; exit 1; fi
GOT_SHA=$(sha256sum "$MODULE" | cut -d' ' -f1)
echo "HEAD   $GOT_HEAD"
echo "MODULE $MODULE"
echo "SHA    $GOT_SHA"
if [ "$GOT_HEAD" != "$EXPECT_HEAD" ]; then echo "PREFLIGHT ABORT: HEAD mismatch"; exit 1; fi
if [ "$GOT_SHA" != "$EXPECT_SHA" ]; then echo "PREFLIGHT ABORT: module sha256 mismatch"; exit 1; fi
echo "PREFLIGHT OK"

if ! command -v lake >/dev/null 2>&1; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none >/dev/null 2>&1
  export PATH="$HOME/.elan/bin:$PATH"
fi
lake --version || { echo "ABORT: no lake"; exit 1; }
lake exe cache get > /content/cache.log 2>&1

echo "=== ISOLATED ELABORATION ==="
lake env lean "$MODULE" > /content/iso.log 2>&1
echo "EXIT $?"
echo "--- BEGIN log (full: no tail, no grep) ---"
cat /content/iso.log
echo "--- END log ---"
