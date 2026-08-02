#!/usr/bin/env bash
# Targeted oracle for S-2a.  Runs only after the module elaborates clean.
#
# The list of declarations to interrogate is GENERATED FROM THE MODULE, never
# hand-written: a hand-written list cannot notice a declaration that was added,
# renamed, or removed, and that is exactly how an oracle silently stops covering
# what it claims to cover.
#
# The checker runs in BOTH normal and optimized mode, because `python -O` removes
# assertions and this repository has already emitted two false PASSes that way.
set -u
export PATH="$HOME/.elan/bin:$PATH"

REPO=/content/repo
BRANCH=claude/congruence-spectrum
MODULE=YangMills/OS/ProjectiveDiameterMonotone.lean
EXPECT_S2A=62c0d58efcc131d83ced138480621101e26e2a2ff4b4fbc8bb6cb38cf178169f
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

lake exe cache get > /content/cache.log 2>&1

echo "=== RE-ELABORATION (must stay clean) ==="
lake env lean "$MODULE" > /content/s2a.log 2>&1
echo "S2A EXIT $?"
echo "--- BEGIN s2a.log ---"
cat /content/s2a.log
echo "--- END s2a.log ---"

echo "=== BUILD THE MODULE'S OLEAN ==="
lake build YangMills.OS.ProjectiveDiameterMonotone > /content/build.log 2>&1
echo "BUILD EXIT $?"
tail -5 /content/build.log

echo "=== ORACLE FILE, GENERATED FROM THE MODULE ==="
echo "import YangMills.OS.ProjectiveDiameterMonotone" > _oracle_s2a.lean
grep -oE '^(theorem|lemma|def|abbrev) [A-Za-z_][A-Za-z0-9_]*' "$MODULE" \
  | awk '{print "#print axioms YangMills.OS.Congruence." $2}' >> _oracle_s2a.lean
cat _oracle_s2a.lean

echo "=== ORACLE ==="
lake env lean _oracle_s2a.lean > /content/oracle_s2a.log 2>&1
echo "ORACLE EXIT $?"
echo "--- BEGIN oracle_s2a.log (full) ---"
cat /content/oracle_s2a.log
echo "--- END oracle_s2a.log ---"

echo "=== RECONCILIATION, normal mode ==="
python3 scripts/check_s2a_oracle.py "$MODULE" /content/oracle_s2a.log
echo "CHECK normal exit $?"

echo "=== RECONCILIATION, optimized mode ==="
python3 -O scripts/check_s2a_oracle.py "$MODULE" /content/oracle_s2a.log
echo "CHECK optimized exit $?"
