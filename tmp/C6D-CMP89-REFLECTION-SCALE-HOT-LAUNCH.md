# Retained-runtime diagnostic: CMP89 reflection scale dictionary

Run only after the active cold C6d gate and its evidence verification, after
the reflection-branch and reflection-orbit hot diagnostics. This is hot
diagnostic evidence and cannot retire PRE-VALIDATION.

```text
cold base source: 77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
scale overlay: f3550512d25ad7a76071a38c421a8c0863986624
runner object: 8323dc229d7b2c8169b85a0b134844fb1e3d0025
runner SHA-256: 8a05126a7a32f8813eaf83323611483afb7af522aec6ee28a5e1ec961bcdb5c7
sentinel: HOT_C6D_CMP89_REFLECTION_SCALE_PASS
```

This supersedes runners `f443e7145fbbb004de236993c5e298ea176eba0c`
and `46273b1824bb7a9d045edccebf7a33edb751dff4`; the current runner also
checks the explicit zero-site witness under positive side lengths.

Execute exactly once in a new cell:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "8323dc229d7b2c8169b85a0b134844fb1e3d0025/"
    "tmp/run_c6d_cmp89_reflection_scale_hot.py"
)
expected = "8a05126a7a32f8813eaf83323611483afb7af522aec6ee28a5e1ec961bcdb5c7"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on first error. PASS verifies only the exact lattice-spacing dictionary
for the two first reflected coordinates, the half-open block carrier fixed by
CMP89 (1.1), and its inclusion in the printed geometric envelope. It does not
prove the Green image-series identity, produce uniform `B0`/`delta0`, or
attain window 15.
