# Retained-runtime diagnostic: normalized CMP89 Neumann precision

Run only after the active C6d Green-owner-prefix gate has emitted a terminal
verdict and, on PASS, its archive and executed notebook have been downloaded
and hash-verified.  This diagnostic mutates the retained checkout and is hot
evidence only; it cannot retire PRE-VALIDATION.

Pinned objects:

```text
cold base source:
  77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
normalized Neumann overlay source:
  b5ace580dae385d1b5c159e2a96993cf3421f4fb
runner object:
  fc1461517467cb8a13dabc95931c9d35803467d4
runner blob SHA-256:
  7e03743155837fcbfc9bd1ce98f432fbeb192e8225e240294c38046864c1a19e
success sentinel:
  HOT_C6D_CMP89_NEUMANN_PRECISION_PASS
```

Execute exactly once in a new cell of the retained runtime:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "fc1461517467cb8a13dabc95931c9d35803467d4/"
    "tmp/run_c6d_cmp89_neumann_precision_hot.py"
)
expected = "7e03743155837fcbfc9bd1ce98f432fbeb192e8225e240294c38046864c1a19e"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on the first error.  A PASS verifies only the normalized internal-bond
operator, energy identity and symmetry in the retained environment.  It does
not prove the `eta^d` measure dictionary, the rectangle/carrier dictionary,
the Green inverse, CMP89 Eq. (2.42), Lemma 2.4, uniform `B0`/`delta0`, or
window 15.
