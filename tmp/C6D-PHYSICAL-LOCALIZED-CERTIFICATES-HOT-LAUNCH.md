# C6d physical-localized certificate hot diagnostic launch

Run this only after the Green-owner cold gate has emitted PASS and its archive
and executed notebook have been preserved.  It reuses that retained Colab
checkout/build.  It is diagnostic evidence only and cannot seal source, move
`20/41`, or attain window 15.

- transport commit: `01598e065f54852a9189266a3e3277c030c20b17`
- runner path: `tmp/c6d_physical_localized_certificates_hot_diagnostic.py`
- runner Git blob: `4b373a222d1b2ed7ea2a0b58c347e120cf388765`
- promoted draft source commit pinned inside runner:
  `4d0340fb794ca0194711d0084ca5aa86a83aa2ce`
- retained checkout: `/content/hrpoly-c6d-green-owner-prefix`

Execute one new cell exactly once:

```python
import pathlib, subprocess

repo = pathlib.Path('/content/hrpoly-c6d-green-owner-prefix')
transport = '01598e065f54852a9189266a3e3277c030c20b17'
runner_rel = 'tmp/c6d_physical_localized_certificates_hot_diagnostic.py'
expected_blob = '4b373a222d1b2ed7ea2a0b58c347e120cf388765'

subprocess.run(
    ['git', 'fetch', '--no-tags', 'origin', transport],
    cwd=repo, check=True)
actual_blob = subprocess.check_output(
    ['git', 'rev-parse', f'{transport}:{runner_rel}'],
    cwd=repo, text=True).strip()
assert actual_blob == expected_blob, (actual_blob, expected_blob)
runner = subprocess.check_output(
    ['git', 'show', f'{transport}:{runner_rel}'], cwd=repo)
runner_path = pathlib.Path('/content/c6d_physical_localized_certificates_hot_diagnostic.py')
runner_path.write_bytes(runner)
result = subprocess.run(['python3', str(runner_path)], cwd=repo)
print(f'HOT_DIAGNOSTIC_EXIT={result.returncode}', flush=True)
```

Stop on the first FAIL.  Preserve the exact stage/error.  On PASS, promote the
six drafts into a new PRE-VALIDATION source checkpoint and run a separate cold
gate before retiring any marker.
