#!/bin/sh
set -u
export GOOGLE_APPLICATION_CREDENTIALS=/mnt/c/Users/lluis/AppData/Roaming/gcloud/application_default_credentials.json
OUT=/mnt/d/Entregas/the-eriksson-programme/2026-11-10_capped-matrix225/attempt-a
CLI=/home/lluis/.local/bin/colab
CFG=/home/lluis/.config/colab-cli/tep225-a-sessions.json
mkdir -p "$OUT"
record_exit() { case "$2" in ''|*[!0-9]*) exit 92;; esac; printf '%s\n' "$2" > "$OUT/$1.tmp"; mv "$OUT/$1.tmp" "$OUT/$1"; }
date -u +%FT%TZ > "$OUT/runtime225-open-requested.txt"
"$CLI" --auth adc --config "$CFG" new -s tep225-a-own-cpu --high-mem > "$OUT/allocation225.log" 2>&1
allocation=$?
record_exit allocation225.exit "$allocation"
if [ "$allocation" -ne 0 ]; then cat "$OUT/allocation225.log"; exit "$allocation"; fi
"$CLI" --auth adc --config "$CFG" exec -s tep225-a-own-cpu -f /mnt/c/Trabajo/the-eriksson-programme/perron-spec-210-20261108/_tmp/run_diagnostic225.py --timeout 1200 > "$OUT/execution225.log" 2>&1
execution=$?
record_exit execution225.exit "$execution"
"$CLI" --auth adc --config "$CFG" download -s tep225-a-own-cpu /content/tep225-diagnostics.zip "$OUT/tep225-diagnostics.zip" > "$OUT/download225.log" 2>&1
download=$?
record_exit download225.exit "$download"
"$CLI" --auth adc --config "$CFG" stop -s tep225-a-own-cpu > "$OUT/release225.log" 2>&1
release=$?
record_exit release225.exit "$release"
date -u +%FT%TZ > "$OUT/runtime225-release-finished.txt"
printf 'ALLOCATION=%s EXECUTION=%s DOWNLOAD=%s RELEASE=%s\n' "$allocation" "$execution" "$download" "$release"
if [ "$execution" -ne 0 ] || [ "$download" -ne 0 ] || [ "$release" -ne 0 ]; then exit 1; fi
