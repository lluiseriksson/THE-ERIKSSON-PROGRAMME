#!/bin/bash
# Fresh-clone verifier for OS-R. CPU high-RAM Colab only; never GPU.
# Usage: bash colab_osr_final_bootstrap.sh <full-40-hex-commit>

set -euo pipefail

SHA="${1:-}"
case "$SHA" in
  [0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]) ;;
  *) echo "FATAL: expected one full lowercase 40-hex commit"; exit 64 ;;
esac

rm -rf /content/eriksson-osr-final
git clone --no-checkout https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git \
  /content/eriksson-osr-final
cd /content/eriksson-osr-final
git checkout --detach "$SHA"
export ERIKSSON_REPO=/content/eriksson-osr-final

curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
source "$HOME/.elan/env"
lake exe cache get || true

set +e
python3 scripts/colab_dobrushin_d4_runner.py "$SHA"
rc=$?
set -e

printf '%d\n' "$rc" > /content/OSR_FINAL_DONE.writing
case "$(cat /content/OSR_FINAL_DONE.writing)" in
  ''|*[!0-9-]*) echo "FATAL: malformed final sentinel"; exit 70 ;;
esac
mv /content/OSR_FINAL_DONE.writing /content/OSR_FINAL_DONE
echo "OSR_FINAL_DONE=$rc"
exit "$rc"
