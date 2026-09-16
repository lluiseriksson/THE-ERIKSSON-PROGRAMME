# Retained-runtime diagnostic: CMP89 reflection-orbit algebra

Run only after the active C6d Green-owner-prefix gate has emitted a terminal
verdict and, on PASS, its archive and executed notebook have been downloaded
and hash-verified. Run the reflection-branch diagnostic before this one. This
diagnostic mutates the retained checkout and is hot evidence only; it cannot
retire PRE-VALIDATION.

Pinned objects:

```text
cold base source:
  77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
reflection-orbit overlay source:
  0428cc5721239578f5c9a8205ec547b61a23ee85
runner object:
  e7cfd5bb9c5b4a0f9d004047bbdef9ce01d0f260
runner blob SHA-256:
  52b8a0097b8b3c9cd84bf0ba6bda74fac0fac2679fc2692a1bb009b8d6e7cbcf
success sentinel:
  HOT_C6D_CMP89_REFLECTION_ORBIT_PASS
```

Execute exactly once in a new cell of the retained runtime:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "e7cfd5bb9c5b4a0f9d004047bbdef9ce01d0f260/"
    "tmp/run_c6d_cmp89_reflection_orbit_hot.py"
)
expected = "52b8a0097b8b3c9cd84bf0ba6bda74fac0fac2679fc2692a1bb009b8d6e7cbcf"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on the first error. A PASS verifies only the integer orbit algebra of the
two one-coordinate reflections printed in CMP89 (2.42), plus its coordinatewise
lift. It does not identify the source rectangle, prove the Green image-series
identity, establish summability or distance decay, settle the endpoint
convention, produce uniform `B0`/`delta0`, or attain window 15.
