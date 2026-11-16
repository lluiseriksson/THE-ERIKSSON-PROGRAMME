#!/usr/bin/env bash
# Prospective Linux-only PDF build. Never execute on Windows.
set -euo pipefail
[[ $(uname -s) == Linux ]] || exit 59
repo_root=$(git rev-parse --show-toplevel)
expected_commit=${1:?exact commit required}
out=${2:?output directory required}
[[ $(git rev-parse HEAD) == "$expected_commit" ]] || exit 60
source_rel='papers/stationary-weighting354/revision-window-20261116/manuscript-window-v2-candidate.tex'
expected_source='186921a56a23015ea43a857adc76631ebbf9f3c3c00e1e3d5566f3f0c31710b3'
printf '%s  %s\n' "$expected_source" "$repo_root/$source_rel" | sha256sum --check --strict -
mkdir -p "$out"
[[ ! -e "$out/driver.tex" ]] || exit 61
cp "$repo_root/$source_rel" "$out/manuscript-window-v2-candidate.tex"
cat > "$out/driver.tex" <<'TEX'
\pdfinfoomitdate=1\relax
\pdftrailerid{}
\pdfsuppressptexinfo=15\relax
\input{manuscript-window-v2-candidate.tex}
TEX
export SOURCE_DATE_EPOCH
SOURCE_DATE_EPOCH=$(git show -s --format=%ct "$expected_commit")
export FORCE_SOURCE_DATE=1 TZ=UTC
printf '%s\n' "$expected_commit" > "$out/source-commit.txt"
printf '%s\n' "$SOURCE_DATE_EPOCH" > "$out/source-date-epoch.txt"
cd "$out"
sha256sum manuscript-window-v2-candidate.tex driver.tex > input-sha256.txt
pdflatex --version > toolchain.txt
latexmk --version >> toolchain.txt
set +e
latexmk -norc -pdf -pdflatex='pdflatex -no-shell-escape %O %S' -interaction=nonstopmode -halt-on-error driver.tex > build-full.log 2>&1
child_rc=$?
set -e
printf '%s\n' "$child_rc" > build-exit-code.tmp
mv build-exit-code.tmp build-exit-code.txt
[[ "$child_rc" -eq 0 ]] || exit "$child_rc"
[[ -s driver.pdf && -s driver.log ]] || exit 62
if grep -Eq 'There were undefined references|Citation .*undefined|Reference .*undefined|multiply defined' driver.log; then
  printf '%s\n' 'POSTCHECK FAILED: unresolved references/citations or duplicate labels' > postcheck.txt
  exit 63
fi
sha256sum driver.pdf > pdf-sha256.txt
pdfinfo driver.pdf > pdfinfo.txt
pdftotext -layout -enc UTF-8 driver.pdf extracted.txt
printf '%s\n' 'Compile returned zero; reference text checks passed; visual and scientific review still required.' > postcheck.txt
