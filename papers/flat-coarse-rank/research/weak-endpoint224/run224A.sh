#!/bin/sh
set -u
export GOOGLE_APPLICATION_CREDENTIALS=/mnt/c/Users/lluis/AppData/Roaming/gcloud/application_default_credentials.json
OUT=/mnt/d/Entregas/the-eriksson-programme/2026-11-10_weak-endpoint224/attempt-a
CLI=/home/lluis/.local/bin/colab
CFG=/home/lluis/.config/colab-cli/tep224-a-sessions.json
mkdir -p "$OUT"
record_exit() { case "$2" in ''|*[!0-9]*) exit 92;; esac; printf '%s\n' "$2" > "$OUT/$1.tmp"; mv "$OUT/$1.tmp" "$OUT/$1"; }
date -u +%FT%TZ > "$OUT/runtime224-open-requested.txt"
"$CLI" --auth adc --config "$CFG" new -s tep224-a-own-cpu --high-mem > "$OUT/allocation224.log" 2>&1
allocation=$?
record_exit allocation224.exit "$allocation"
if [ "$allocation" -ne 0 ]; then cat "$OUT/allocation224.log"; exit "$allocation"; fi
"$CLI" --auth adc --config "$CFG" exec -s tep224-a-own-cpu -f /mnt/c/Trabajo/the-eriksson-programme/perron-spec-210-20261108/_tmp/run_diagnostic224.py --timeout 1200 > "$OUT/execution224.log" 2>&1
execution=$?
record_exit execution224.exit "$execution"
"$CLI" --auth adc --config "$CFG" download -s tep224-a-own-cpu /content/tep224-diagnostics.zip "$OUT/tep224-diagnostics.zip" > "$OUT/download224.log" 2>&1
download=$?
record_exit download224.exit "$download"
"$CLI" --auth adc --config "$CFG" stop -s tep224-a-own-cpu > "$OUT/release224.log" 2>&1
release=$?
record_exit release224.exit "$release"
date -u +%FT%TZ > "$OUT/runtime224-release-finished.txt"
printf 'ALLOCATION=%s EXECUTION=%s DOWNLOAD=%s RELEASE=%s\n' "$allocation" "$execution" "$download" "$release"
if [ "$execution" -ne 0 ] || [ "$download" -ne 0 ] || [ "$release" -ne 0 ]; then exit 1; fi
