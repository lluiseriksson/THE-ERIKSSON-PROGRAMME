#!/usr/bin/env bash
set -euo pipefail

result_file=${1:?result-file argument is required}
comparison_root=${2:?comparison-root argument is required}
change_base=${3:?change-base argument is required}

# This must remain the first effective guard action. A failure while resolving
# or materializing the comparison must never leave a prior PASS publishable.
rm -f -- "$result_file"
test ! -e "$result_file"

worktree_added=0
cleanup() {
  if [[ "$worktree_added" -eq 1 ]]; then
    git worktree remove --force "$comparison_root"
  fi
}
trap cleanup EXIT

git worktree add --detach "$comparison_root" "$change_base"
worktree_added=1

python scripts/validate_run_manifests.py \
  --require-nonempty \
  --baseline .github/run-manifest-debt-baseline.json \
  --comparison-root "$comparison_root" \
  --result-file "$result_file"
