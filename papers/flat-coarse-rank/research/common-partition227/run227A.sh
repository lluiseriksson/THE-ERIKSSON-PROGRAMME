#!/bin/sh
set -u
export GOOGLE_APPLICATION_CREDENTIALS=/mnt/c/Users/lluis/AppData/Roaming/gcloud/application_default_credentials.json
OUT=/mnt/d/Entregas/the-eriksson-programme/2026-11-10_common-partition227/attempt-a
CLI=/home/lluis/.local/bin/colab
CFG=/home/lluis/.config/colab-cli/tep227-a-sessions.json
mkdir -p "$OUT"
record_exit() { case "$2" in ''|*[!0-9]*) exit 92;; esac; printf '%s\n' "$2" > "$OUT/$1.tmp"; mv "$OUT/$1.tmp" "$OUT/$1"; }
date -u +%FT%TZ > "$OUT/runtime227-open-requested.txt"
"$CLI" --auth adc --config "$CFG" new -s tep227-a-own-cpu --high-mem > "$OUT/allocation227.log" 2>&1
allocation=$?
record_exit allocation227.exit "$allocation"
if [ "$allocation" -ne 0 ]; then cat "$OUT/allocation227.log"; exit "$allocation"; fi
"$CLI" --auth adc --config "$CFG" exec -s tep227-a-own-cpu -f /mnt/c/Trabajo/the-eriksson-programme/perron-spec-210-20261108/_tmp/run_diagnostic227.py --timeout 1200 > "$OUT/execution227.log" 2>&1
execution=$?
record_exit execution227.exit "$execution"
"$CLI" --auth adc --config "$CFG" download -s tep227-a-own-cpu /content/tep227-diagnostics.zip "$OUT/tep227-diagnostics.zip" > "$OUT/download227.log" 2>&1
download=$?
record_exit download227.exit "$download"
"$CLI" --auth adc --config "$CFG" stop -s tep227-a-own-cpu > "$OUT/release227.log" 2>&1
release=$?
record_exit release227.exit "$release"
date -u +%FT%TZ > "$OUT/runtime227-release-finished.txt"
printf 'ALLOCATION=%s EXECUTION=%s DOWNLOAD=%s RELEASE=%s\n' "$allocation" "$execution" "$download" "$release"
if [ "$execution" -ne 0 ] || [ "$download" -ne 0 ] || [ "$release" -ne 0 ]; then exit 1; fi
