# Retained-runtime diagnostic: CMP89 reflection representation interface

Run only after the active cold C6d gate and evidence verification, after the
reflection branch, orbit, and scale diagnostics. Hot evidence cannot retire
PRE-VALIDATION.

```text
cold base: 77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
overlay: f33df6a0c56a83925f4378f5cd071f88c2e4e8f6
runner: 9e936ef29cbcca1ebbb8668845180a65917e3d34
runner SHA-256: ff3f5462e1ce0057ad555e221c4484c054fdb4fa3732c645c613a29770d1ba8f
sentinel: HOT_C6D_CMP89_REFLECTION_REPRESENTATION_PASS
```

Execute exactly once:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "9e936ef29cbcca1ebbb8668845180a65917e3d34/"
    "tmp/run_c6d_cmp89_reflection_representation_hot.py"
)
expected = "ff3f5462e1ce0057ad555e221c4484c054fdb4fa3732c645c613a29770d1ba8f"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on first error. PASS verifies only the type-level source gate and its
explicit series. Summability and equality with the physical regional Green
remain obligations; no `B0`, `delta0`, or window 15 is produced.
