#!/usr/bin/env bash
# Targeted oracle for ONE module.  Generalised from scripts/s2a_oracle.sh.
#
# The declaration list is GENERATED FROM THE MODULE, never hand-written: a
# hand-written list cannot notice a declaration that was added, renamed or
# removed, which is how an oracle silently stops covering what it claims to.
# The checker runs in BOTH normal and optimized mode, because `python -O` removes
# assertions and this repository has already emitted two false PASSes that way.
#
# Required in the environment: EXPECT_HEAD, MODULE, EXPECT_SHA, NAMESPACE
set -u
export PATH="$HOME/.elan/bin:$PATH"

REPO=/content/repo
BRANCH=claude/congruence-spectrum
EXPECT_HEAD="${EXPECT_HEAD:-}"
MODULE="${MODULE:-}"
EXPECT_SHA="${EXPECT_SHA:-}"
NAMESPACE="${NAMESPACE:-}"

for v in EXPECT_HEAD MODULE EXPECT_SHA NAMESPACE; do
  eval "val=\$$v"
  if [ -z "$val" ]; then echo "PREFLIGHT ABORT: $v not supplied"; exit 1; fi
done

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

lake exe cache get > /content/cache.log 2>&1
MODNAME=$(echo "${MODULE%.lean}" | tr '/' '.')

echo "=== RE-ELABORATION (must stay clean) ==="
lake env lean "$MODULE" > /content/iso.log 2>&1
echo "EXIT $?"
echo "--- BEGIN log ---"
cat /content/iso.log
echo "--- END log ---"

echo "=== BUILD ==="
lake build "$MODNAME" > /content/build.log 2>&1
echo "BUILD EXIT $?"
tail -3 /content/build.log

echo "=== ORACLE FILE, GENERATED FROM THE MODULE ==="
echo "import $MODNAME" > _oracle_iso.lean
grep -oE '^(theorem|lemma|def|abbrev) [A-Za-z_][A-Za-z0-9_]*' "$MODULE" \
  | awk -v ns="$NAMESPACE" '{print "#print axioms " ns "." $2}' >> _oracle_iso.lean
wc -l _oracle_iso.lean

echo "=== ORACLE ==="
lake env lean _oracle_iso.lean > /content/oracle_iso.log 2>&1
echo "ORACLE EXIT $?"

echo "=== RECONCILIATION, normal mode ==="
python3 scripts/check_s2a_oracle.py "$MODULE" /content/oracle_iso.log
echo "CHECK normal exit $?"

echo "=== RECONCILIATION, optimized mode ==="
python3 -O scripts/check_s2a_oracle.py "$MODULE" /content/oracle_iso.log
echo "CHECK optimized exit $?"
