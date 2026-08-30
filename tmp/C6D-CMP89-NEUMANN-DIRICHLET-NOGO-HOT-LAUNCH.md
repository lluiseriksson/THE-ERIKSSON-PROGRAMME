# Retained-runtime diagnostic: CMP89 Neumann/Dirichlet boundary no-go

Run only after the active C6d Green-owner-prefix gate has emitted a terminal
verdict and, on PASS, its archive and executed notebook have been downloaded
and hash-verified. This diagnostic mutates the retained checkout and is hot
evidence only; it cannot retire PRE-VALIDATION.

Pinned objects:

```text
cold base source:
  77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
boundary no-go overlay source:
  66ec112e8b25b3db92b38bcc5c3ae36c7d6c4f48
runner object:
  df173dc9cfe3b9399a4502dbc09da61ac55edc9d
runner blob SHA-256:
  ac09bf310720b46fd06b03935ab043e0aace80a703ccbc1ff5f6a0305a701ca6
success sentinel:
  HOT_C6D_CMP89_NEUMANN_DIRICHLET_NOGO_PASS
```

Execute exactly once in a new cell of the retained runtime, after the three
earlier queued diagnostics have passed:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "df173dc9cfe3b9399a4502dbc09da61ac55edc9d/"
    "tmp/run_c6d_cmp89_neumann_dirichlet_nogo_hot.py"
)
expected = "ac09bf310720b46fd06b03935ab043e0aace80a703ccbc1ff5f6a0305a701ca6"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on the first error. A PASS verifies only the exact derivative-level
boundary mismatch: a boundary-crossing bond is absent from the internal-bond
Neumann carrier but is charged by the zero-extension Dirichlet derivative.
It does not compare Laplacian norms or Green functions, construct the CMP89
rectangle, prove the multiple-reflection representation (2.42), provide an
image-orbit or distance dictionary, prove uniform `B0`/`delta0`, or attain
window 15.
