# Eq. (3.59) real-slice cold gate — FAIL v1

- source SHA: `e0a2b346ceeb88f476cc80c53df7210b74ae77e0`
- runner revision: `eq359-real-slice-promoted-cold-v1`
- opened UTC: `2026-08-26T12:21:59.033626+00:00`
- closed UTC: `2026-08-26T12:55:47.270484+00:00`
- final status: `FAIL`
- first failing stage:
  `eq359_real_slice_01_balabancmp99specialunitarytospeciallinearrealslice_source`
- canonical evidence JSON SHA-256:
  `8FDA049F61CB0CB1EC1DF71C97BE8F1F40BB4E28CAAFE012F9FF11832FC0DC8E`
- downloaded archive SHA-256:
  `84FBC65EA5448BFD244A460FC5BDCDA66E337E24A1864C8689DF4DBE761972CB`

The archive hash was independently recomputed on Windows and matches the
hash printed by Colab.  The gate failed before any Eq. (3.59) real-slice
module or audit could be sealed.  The first compiler error was a parser-safe
notation defect in the compact inverse theorem; the retained runtime was
used only for stop-on-first-error diagnostics.
