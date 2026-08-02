#!/usr/bin/env bash
set -euo pipefail

TARGET="916de45a6d09df417e2af4e10f080f0521498fb2"
P="YangMills/OS/DobrushinOscillation.lean"
EXPECT="87ac87f63f9fe442230d84a7208e1735bbb7180334af67572df29c36838019c3"

echo "=== environment identity ==="
uname -a
git --version

rm -rf "$HOME/d3a-audit-2"
git clone --quiet --no-checkout --single-branch \
  --branch davinci/dobrushin-uniform \
  https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git \
  "$HOME/d3a-audit-2"
cd "$HOME/d3a-audit-2"

echo "=== git config in this checkout ==="
git config --show-origin --get core.autocrlf || echo "core.autocrlf <unset>"
git config --show-origin --get core.eol || echo "core.eol <unset>"

git checkout --detach "$TARGET" 2>&1 | tail -1

echo "=== identities ==="
commit=$(git rev-parse HEAD)
blob=$(git rev-parse "HEAD:$P")
working_blob=$(git hash-object --no-filters "$P")
canonical=$(git cat-file blob "$blob" | sha256sum | cut -d' ' -f1)
materialized=$(sha256sum "$P" | cut -d' ' -f1)

echo "commit=$commit"
echo "blob=$blob"
echo "working_blob=$working_blob"
echo "canonical=$canonical"
echo "materialized=$materialized"

echo "=== status / diff / attrs ==="
git status --porcelain=v1 --untracked-files=all
echo "(status end)"
git diff --no-ext-diff --exit-code HEAD -- "$P" && echo "diff: clean"
git check-attr -a -- "$P"
echo "(attr end)"

echo "=== gates ==="
test "$commit" = "$TARGET" && echo "OK commit"
test "$blob" = "$working_blob" && echo "OK raw blob equality"
test "$canonical" = "$materialized" && echo "OK canonical == materialized"
test "$canonical" = "$EXPECT" && echo "OK reproduces the declared canonical hash"
echo "CHECKOUT 2 IDENTITY PASSED"
