# C6d retained-runtime post-cold runbook

Status: execution instructions only.  Neither hot queue is seal evidence.

## Entry gate

Proceed only after the already-running notebook emits literal
`FINAL_STATUS=PASS`.  Do not rerun its cell.  Before changing the checkout,
preserve and download:

- `/content/hrpoly-c6d-source-coercivity-green-evidence.tar.gz`;
- the executed notebook;
- the printed archive hash and final sentinel.

Verify the archive locally with
`tmp/verify_c6d_source_coercivity_green_evidence.py`.  The cold source must be
`2bb3eb7325b621954a7132d0a8bab3ce2c1bdf24`.

## Hot queue 1: six full-companion/compression pairs

Runner object:
`3b2c385803a75111099cc451e8ed4400f8dbf8c0:tmp/c6d_full_companion_hot_queue.py`

SHA-256:
`cafb9dba5954b388ff0b8e9f7c8e1c721dfd82d78a8227c2c9a0aacb756b759d`

The runner itself checks out exact source
`76bfe9c82ffd1e409d1c673b68324449171b3318` while preserving `.lake`.
Execute it once in a new Colab cell:

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/3b2c385803a75111099cc451e8ed4400f8dbf8c0/tmp/c6d_full_companion_hot_queue.py"
expected = "cafb9dba5954b388ff0b8e9f7c8e1c721dfd82d78a8227c2c9a0aacb756b759d"
payload = urllib.request.urlopen(url, timeout=60).read()
actual = hashlib.sha256(payload).hexdigest()
assert actual == expected, (actual, expected)
path = pathlib.Path("/content/c6d_full_companion_hot_queue.py")
path.write_bytes(payload)
try:
    runpy.run_path(str(path), run_name="__main__")
except SystemExit as exc:
    if exc.code not in (None, 0):
        raise
```

Stop at its first real error.  Continue to queue 2 only on literal hot
`FINAL_STATUS=PASS`.

## Hot queue 2: ambient C6d producer plus active-region transport

Runner object:
`d2ae1536739da416e0e1200e9cd047222a65fcea:tmp/c6d_ambient_region_hot_diagnostic.py`

SHA-256:
`39d2b18ef7e5e836406453bd0aa4337fa2d06155d1aaf04de0e93b7ae9d56297`

The runner checks out exact scratch source
`a51130ceda1be5c325d8b7211ec2e4b0dfc22a22`, materializes the two source/audit
pairs under their intended module names, expects 10 carrier-transport and 7
ambient-producer axiom headers, and rejects anything outside
`{propext, Classical.choice, Quot.sound}`.

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/d2ae1536739da416e0e1200e9cd047222a65fcea/tmp/c6d_ambient_region_hot_diagnostic.py"
expected = "39d2b18ef7e5e836406453bd0aa4337fa2d06155d1aaf04de0e93b7ae9d56297"
payload = urllib.request.urlopen(url, timeout=60).read()
actual = hashlib.sha256(payload).hexdigest()
assert actual == expected, (actual, expected)
path = pathlib.Path("/content/c6d_ambient_region_hot_diagnostic.py")
path.write_bytes(payload)
try:
    runpy.run_path(str(path), run_name="__main__")
except SystemExit as exc:
    if exc.code not in (None, 0):
        raise
```

Preserve both hot evidence directories before releasing the runtime.  Hot
PASS authorizes only preparation of corrected PRE-VALIDATION promotion; a
later cold checkout is required to seal.  Neither queue moves `20/41`,
attains window 15, or instantiates `TermSource`.
