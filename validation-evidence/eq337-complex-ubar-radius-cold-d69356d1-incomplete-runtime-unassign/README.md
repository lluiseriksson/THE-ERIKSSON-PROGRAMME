# Eq. (3.37) complex Ubar radius — incomplete transport incident

This directory preserves the visible tail of a mathematically successful cold
Colab run. It is **not accepted sealing evidence** because the launcher called
`runtime.unassign()` immediately after `FINAL_STATUS=PASS`, before the evidence
archive could be downloaded. Colab then attached a new runtime and retained
only the last 5,000 streamed lines.

- source SHA: `d69356d18c6c2392bc8a9599fd1c398109487f57`
- runner checkpoint: `ad2be23521f22ab0eadba2fc795698cd6f16e5fc`
- runner revision: `eq337-complex-ubar-radius-promoted-cold-v5`
- runner SHA-256: `33523514d81937be93e92cceef98f367c7f46080bbbc1e413238b06180e01572`
- root: `Build completed successfully (10960 jobs)`
- root stage: `complex_ubar_radius_promoted_root`, exit `0`, `11060.127` s
- reported evidence SHA-256: `8b5078435bfa3f57bf0259f3c7347edd6dc8d5d18e71b0153b4d32254bcff731`
- reported archive SHA-256: `7c9e680c44d27c111736f7e3158eb57a8891e07842ffd2d41a52af8430610ba4`
- terminal markers: `FINAL_STATUS=PASS`, `LAUNCHER_EXIT=0`

Preserved files:

- `colab-visible-last-5000-lines.txt`: SHA-256
  `AA3672C8BF9C98D0533ADB99D0AE604E91AF3A9848274DB07B09044D1D7B0D1D`
- `executed-notebook-truncated.ipynb`: SHA-256
  `6154FFFA1F93449CB6FDDE52DBAB67F37D76DFC0BC08D6B8467B1DA91B86E561`

The strict packager correctly rejected this transport because the retained
tail no longer contains the unique `RUNNER_REV` and early focal/audit stage
markers. No seal or counter movement may cite this directory. A controlled
rerun must retain the runtime until the archive is downloaded and verified.
