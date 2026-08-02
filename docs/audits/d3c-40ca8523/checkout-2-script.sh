#!/usr/bin/env bash
set -euo pipefail

TARGET="40ca85239cb14f18ebf16aa46769f3bc02bbaf6b"
P="YangMills/OS/DobrushinComparison.lean"
EXPECT_BLOB="3fe356cc97e57f2d241158b692e6b8a3acece83a"
EXPECT_SHA="698080fa80ea44d2f1ae7b46cab333b5d0d6f4b97d205df2844db69d510017ea"

echo "=== environment identity ==="
uname -a
git --version
echo "elan present: $(command -v elan >/dev/null 2>&1 && echo yes || echo no)"
echo "lake present: $(command -v lake >/dev/null 2>&1 && echo yes || echo no)"

rm -rf "$HOME/d3c-audit-2"
git clone --quiet --depth 1 --single-branch --branch davinci/dobrushin-d3c \
  https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git "$HOME/d3c-audit-2"
cd "$HOME/d3c-audit-2"

echo "=== git config in this checkout ==="
git config --show-origin --get core.autocrlf || echo "core.autocrlf <unset>"
git config --show-origin --get core.eol || echo "core.eol <unset>"

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
git diff --no-ext-diff --exit-code HEAD -- "$P" > /dev/null && echo "diff: clean"
git check-attr -a -- "$P"
echo "(attr end)"

echo "=== gates ==="
test "$commit" = "$TARGET"        && echo "OK commit == A"
test "$blob" = "$EXPECT_BLOB"     && echo "OK blob == 3fe356cc"
test "$blob" = "$working_blob"    && echo "OK RAW EQUALITY"
test "$canonical" = "$materialized" && echo "OK canonical == materialized"
test "$canonical" = "$EXPECT_SHA" && echo "OK SHA-256 REPRODUCED: 698080fa"
echo ""
echo "Lean build      NOT RUN"
echo "Axiom audit     NOT RUN"
echo "Warning policy  NOT EXERCISED"
echo "CHECKOUT 2 IDENTITY PASSED"
