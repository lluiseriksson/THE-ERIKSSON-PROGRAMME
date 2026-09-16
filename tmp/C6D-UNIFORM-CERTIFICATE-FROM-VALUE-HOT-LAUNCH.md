# Retained-runtime hot diagnostic: uniform Eq. (3.42) certificate from value

This diagnostic may run only after the C6d Green owner-prefix cold gate has
emitted `FINAL_STATUS=PASS` and both its evidence archive and executed
notebook have been downloaded and hash-verified.  It mutates the completed
cold checkout and is therefore diagnostic evidence only, never part of the
cold seal.

Pinned objects:

```text
cold base source:
  77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
two-file overlay source:
  737e2f8149cde16a9d0ea876009f9c83dd144dea
runner object:
  ba317e24fb2f7386bc3ab2262bc23322c041209f
runner blob SHA-256:
  697136D12204A3F0B7C00D8B210EBCD6E974ACCF494D8E0087B622444851FB5E
success sentinel:
  HOT_C6D_UNIFORM_CERTIFICATE_FROM_VALUE_PASS
```

Execute once in a new cell of the retained runtime:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "ba317e24fb2f7386bc3ab2262bc23322c041209f/"
    "tmp/run_c6d_uniform_certificate_from_value_hot.py"
)
expected = "697136d12204a3f0b7c00d8b210ebcd6e974accf494d8e0087b622444851fb5e"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop at the first failure.  A PASS permits proof repair/promotion planning;
it does not retire either PRE-VALIDATION marker, move `20/41`, construct a
uniform regional value estimate, attain window 15 or instantiate a
`TermSource`.
