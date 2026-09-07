"""Independent bounded HOT evidence check; does not authorize a cold seal."""
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
import tarfile

archive, expected, repo = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
assert archive.stat().st_size <= 8 * 1024 * 1024
assert hashlib.sha256(archive.read_bytes()).hexdigest() == expected.lower()
files = {}
with tarfile.open(archive, 'r:gz') as tar:
    members = tar.getmembers()
    assert len(members) <= 20
    assert sum(m.size for m in members) <= 64 * 1024 * 1024
    for m in members:
        if m.isdir():
            assert m.name == 'neumann-full-flag-hot-v2'
            continue
        assert m.isfile() and not m.issym() and not m.islnk()
        parts = Path(m.name).parts
        assert len(parts) == 2 and parts[0] == 'neumann-full-flag-hot-v2'
        assert parts[1] not in files
        files[parts[1]] = tar.extractfile(m).read()
report = json.loads(files['result.json'])
assert report['cold_seal'] is False
assert report['source_base'] == 'f0c58431d20042ced9177632409e9f9bcbe79692'
assert report['status'] in ('PASS', 'FAIL')
for name, digest in report['source_overlays'].items():
    assert hashlib.sha256(files[name]).hexdigest() == digest
    original = name.replace('V2.lean', '.lean')
    blob = subprocess.check_output(['git', 'cat-file', 'blob',
        report['source_base'] + ':tmp/' + original], cwd=repo)
    assert files[name] == blob.replace(b'Nat.cast_mul', b'Int.natCast_mul')
sys.path.insert(0, str(repo / 'scripts'))
import full_green_owner_exact_axiom_gate as gate
assert hashlib.sha256((repo / 'scripts/full_green_owner_exact_axiom_gate.py').read_bytes().replace(b'\r\n', b'\n')).hexdigest() == '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
names = {'YangMills.RG.' + s for s in ['neumannPhysicalFullFlag_iff',
    'neumannPhysicalFullFlag_scale_test', 'neumannPhysicalFullFlag_scale',
    'neumannPhysicalFullFlag_outgoing', 'neumannPhysicalFullFlag_incoming']}
commands = [
    ('repro', ['lake', 'env', 'lean', 'tmp/NeumannFullFlagCastReproV2.lean']),
    ('prerequisite', ['lake', 'build', 'YangMills.RG.NeumannRectangleDirectionalMasks']),
    ('draft', ['lake', 'env', 'lean', 'tmp/NeumannPhysicalFullFlagDraftV2.lean'])]
assert 1 <= len(report['records']) <= 3
for rec, (stage, command) in zip(report['records'], commands):
    assert rec['stage'] == stage and rec['command'] == command
    assert math.isfinite(rec['seconds']) and rec['seconds'] >= 0
    log = files[stage + '.log']
    assert hashlib.sha256(log).hexdigest() == rec['log_sha256']
    if rec['exit'] == 0 and stage != 'prerequisite':
        actual = gate.exact_axioms(log.decode(), {'fullFlagScaleCastRepro'} if stage == 'repro' else names)
        assert actual == report['audits'][stage]
if report['status'] == 'PASS':
    assert len(report['records']) == 3
    assert all(r['exit'] == 0 for r in report['records'])
print(json.dumps(report, sort_keys=True))
print('INDEPENDENT_HOT_EVIDENCE_OK; cold_seal=False')
