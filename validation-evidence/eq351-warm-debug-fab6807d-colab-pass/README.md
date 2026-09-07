# Eq351 warm Colab debug checkpoint

This is diagnostic evidence, not a cold seal and not a counter-moving result.
On source checkpoint `fab6807d1ddde2e33b5d350a14ba6dd47b61745b`, the
20-stage queue in `scripts/colab_eq351_warm_debug.py` returned launcher exit
zero after 291.860 seconds in the retained C6d Colab runtime.

The same runtime was used intentionally to iterate only from the first failed
target.  Earlier failed cells remain in the downloaded notebook so the repair
history is not erased.  The final coherent pass is identified by:

```text
EQ351_FULL_WARM_HEAD=fab6807d1ddde2e33b5d350a14ba6dd47b61745b
EQ351_FULL_WARM_LAUNCHER_EXIT=0 SECONDS=291.860
```

This checkpoint proves neither a fresh-clone seal nor Eq. (3.51) as a source
identity.  PRE-VALIDATION remains in place; `20/41` and `TermSource = 0` do
not move.

