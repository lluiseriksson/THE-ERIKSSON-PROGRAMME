#!/usr/bin/env bash
# Prospective only; new owner exception and capacity verification required.
set -euo pipefail
[[ $(uname -s) == Linux ]] || exit 59
root=${1:?evidence directory}
sha=${2:?exact commit}
phase() {
  local name=$1
  shift
  date -u +%FT%TZ > "$root/${name}-start.txt"
  local rc=0
  "$@" > "$root/${name}-full.log" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "$root/${name}-exit.txt"
  date -u +%FT%TZ > "$root/${name}-end.txt"
  return "$rc"
}
record_pipeline_exit() {
  local rc=$?
  printf '%s\n' "$rc" > "$root/pipeline-exit.txt"
  date -u +%FT%TZ > "$root/pipeline-end.txt"
}
trap record_pipeline_exit EXIT
rel=papers/stationary-weighting354/revision-window-20261116
cd "$GITHUB_WORKSPACE/clone-a"
phase build-a bash "$rel/build-one.sh" "$sha" "$root/a"
cd "$GITHUB_WORKSPACE/clone-b"
phase build-b bash "$rel/build-one.sh" "$sha" "$root/b"
phase compare cmp "$root/a/driver.pdf" "$root/b/driver.pdf"
printf '%s\n' 'Two fresh checkouts, same runner/toolchain: PDF bytes match. No mathematical or visual verification implied.' > "$root/reproducibility.txt"
mkdir -p "$root/pages"
phase render pdftoppm -r 120 -png "$root/a/driver.pdf" "$root/pages/page"
expected=$(awk '/^Pages:/ {print $2}' "$root/a/pdfinfo.txt")
actual=$(find "$root/pages" -maxdepth 1 -type f -name 'page-*.png' | wc -l)
printf 'Expected pages: %s\nRendered images: %s\n' "$expected" "$actual" > "$root/page-count.txt"
if [[ "$expected" =~ ^[0-9]+$ && "$expected" -gt 0 && "$actual" -eq "$expected" ]]; then
  printf '0\n' > "$root/page-count-exit.txt"
else
  printf '65\n' > "$root/page-count-exit.txt"
  exit 65
fi
printf '%s\n' 'Rendering and count passed; every page still requires visual review.' > "$root/render-status.txt"
