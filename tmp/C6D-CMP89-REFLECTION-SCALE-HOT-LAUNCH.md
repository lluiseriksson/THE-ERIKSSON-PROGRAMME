# Retained-runtime diagnostic: CMP89 reflection scale dictionary

Run only after the active cold C6d gate and its evidence verification, after
the reflection-branch and reflection-orbit hot diagnostics. This is hot
diagnostic evidence and cannot retire PRE-VALIDATION.

```text
cold base source: 77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
scale overlay: 7314d0f57d8025f21e43c506ebd853126a396a99
runner object: f443e7145fbbb004de236993c5e298ea176eba0c
runner SHA-256: e81d19d273edf5f3876a15d2178ce26cd0f92a3c8943f0edc136393d10c64190
sentinel: HOT_C6D_CMP89_REFLECTION_SCALE_PASS
```

Execute exactly once in a new cell:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "f443e7145fbbb004de236993c5e298ea176eba0c/"
    "tmp/run_c6d_cmp89_reflection_scale_hot.py"
)
expected = "e81d19d273edf5f3876a15d2178ce26cd0f92a3c8943f0edc136393d10c64190"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on first error. PASS verifies only the exact lattice-spacing dictionary
for the two first reflected coordinates and the literal inclusive integer
rectangle. It does not choose the period/site count hidden in the ellipsis,
prove the Green image-series identity, produce uniform `B0`/`delta0`, or
attain window 15.
