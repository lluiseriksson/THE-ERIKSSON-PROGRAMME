# K4 current-regeneration hash drift (2026-07-24)

The 15-unit `_current_regen` t-box archive was compared against the
historical candidate with `scripts/compare_surface_remainder_k4_tbox_current_regen.py`.
All 34,560 cells and every mathematical line agree after removing only the
provenance and carrier-dependency lines; production/replay pairs are
byte-identical.

The authoritative dependency audit nevertheless rejects the archive because
the transcripts record carrier hash
`59343fa26b1b16fdb4f7d91f8e43fa05dbe8c12740e771df0a62ef1206acdd2a`, while the
current worktree carrier hashes to
`8B21C9592F036021F33B99D7DB58747E82DAF252CFD3B8A8200C46F7DB901B51`.
The failure is therefore provenance-only but real: the regenerated files are
not current-head evidence until rerun against the present carrier.  They stay
quarantined and carry no K4, S1'''/S2''', G2, or G6 load.
