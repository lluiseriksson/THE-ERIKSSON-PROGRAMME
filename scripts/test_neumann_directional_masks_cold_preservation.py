"""In-memory nested archive fixtures only. No Lean/network/disk evidence writes."""
import argparse
import contextlib
import copy
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import types
from unittest.mock import patch

sys.path.insert(0, 'scripts')
import preserve_neumann_directional_masks_cold as p


def blob(ref, name):
    return subprocess.check_output(['git', 'cat-file', 'blob',
        ref + ':scripts/' + name], timeout=5)


helpers = {name: blob(ref, name) for name, (ref, _) in p.PINS.items()}
cold = p.load(helpers['verify_neumann_directional_masks_promoted_cold.py'],
    'verify_neumann_directional_masks_promoted_cold.py')
old = p.load(helpers['verify_cmp99_full_green_residue_cold.py'],
    'verify_cmp99_full_green_residue_cold.py')
gate = p.load(helpers['full_green_owner_exact_axiom_gate.py'],
    'full_green_owner_exact_axiom_gate.py')
captured = []
original = cold.verify


def capture(files, gate_arg, old_arg):
    result = original(files, gate_arg, old_arg)
    captured.append(copy.deepcopy(files))
    return result


cold.verify = capture
with contextlib.redirect_stdout(io.StringIO()):
    cold.self_test(gate, old)
cold.verify = original
inner = captured[0]


def archive(files):
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode='w:gz') as out:
        for name, data in files.items():
            entry = tarfile.TarInfo(name)
            entry.size = len(data)
            out.addfile(entry, io.BytesIO(data))
    return stream.getvalue()


prefix = p.REV + '-launch/'
inner_name = 'hrpoly-' + p.REV + '-evidence.tar.gz'
inner_prefix = 'hrpoly-' + p.REV + '-evidence/'
inner_blob = archive({inner_prefix + n: b for n, b in inner.items()})
launcher = blob('2fde75090c4d98f6617bcaa88e12320d9c2c76eb', p.LAUNCHER)
assert p.sha(launcher) == p.LAUNCHER_HASH
outer = {p.LAUNCHER: launcher, inner_name: inner_blob,
    **{prefix + n: b for n, b in helpers.items()}}
outer[prefix + 'transport.json'] = json.dumps(p.PINS).encode()
outer[prefix + 'launch-final-status.json'] = json.dumps(dict(
    status='PASS', source=p.SOURCE, revision=p.REV, cold_seal=True)).encode()
work = '/content/' + prefix
py = '/usr/bin/python3'
verifier = work + 'verify_neumann_directional_masks_promoted_cold.py'
commands = [
    ('verifier_self_test', [py, verifier, '--helpers', work.rstrip('/'), '--self-test']),
    ('physical_cold_graph', [py, work + 'colab_neumann_directional_masks_promoted_cold.py']),
    ('archive_verifier', [py, verifier, '--helpers', work.rstrip('/'),
        '--archive', '/content/' + inner_name, '--sha256', p.sha(inner_blob)]),
]
records = []
for stage, command in commands:
    log = b'SYNTHETIC ONLY, NOT COMPILER EVIDENCE'
    outer[prefix + stage + '.log'] = log
    records.append(dict(stage=stage, command=command, exit=0, seconds=.01,
        log_sha256=p.sha(log)))
outer[prefix + 'launch-records.json'] = json.dumps(records).encode()


class MemoryArchive:
    def __init__(self, data):
        self.data = data
    def stat(self):
        return types.SimpleNamespace(st_size=len(self.data))
    def read_bytes(self):
        return self.data


def verify_outer(files):
    data = archive(files)
    args = argparse.Namespace(archive=MemoryArchive(data),
        outer_sha256=p.sha(data), destination=None)
    output = io.StringIO()
    with patch.object(argparse.ArgumentParser, 'parse_args', return_value=args):
        with contextlib.redirect_stdout(output):
            p.main()
    assert 'NEUMANN_DIRECTIONAL_MASKS_COLD_PRESERVED COMPILER_SEAL=1' in output.getvalue()
    # This label is tested inside captured synthetic stdout, never published
    # as actual evidence. No fixture is written to validation-evidence.


verify_outer(outer)
bads = []
bad = dict(outer); bad[p.LAUNCHER] += b'changed'; bads.append(bad)
bad = dict(outer); bad[prefix + 'physical_cold_graph.log'] += b'changed'; bads.append(bad)
bad = dict(outer); bad['unexpected.txt'] = b'extra'; bads.append(bad)
bad = dict(outer); del bad[inner_name]; bads.append(bad)
bad = dict(outer)
bad[prefix + 'launch-final-status.json'] = json.dumps(dict(
    status='FAIL', source=p.SOURCE, revision=p.REV, cold_seal=True)).encode()
bads.append(bad)
for index in range(3):
    bad = dict(outer); changed = copy.deepcopy(records); changed[index]['exit'] = 1
    bad[prefix + 'launch-records.json'] = json.dumps(changed).encode()
    bads.append(bad)
bad = dict(outer); changed = copy.deepcopy(records); changed[0]['command'][0] = '/unknown/python'
bad[prefix + 'launch-records.json'] = json.dumps(changed).encode(); bads.append(bad)
bad = dict(outer); changed = dict(inner)
changed['NeumannRectangleDirectionalMasks.olean'] += b'corrupt'
bad[inner_name] = archive({inner_prefix + n:b for n,b in changed.items()})
changed_records = copy.deepcopy(records)
changed_records[-1]['command'][-1] = p.sha(bad[inner_name])
bad[prefix + 'launch-records.json'] = json.dumps(changed_records).encode()
bads.append(bad)
for i, bad in enumerate(bads):
    try:
        verify_outer(bad)
    except (ValueError, KeyError, AssertionError):
        continue
    raise AssertionError('CORRUPT_OUTER_ACCEPTED=' + str(i))
print('DIRECTIONAL_MASKS_COLD_PRESERVATION_SELF_TEST=PASS valid=1 rejected=' + str(len(bads)))
print('SYNTHETIC_ONLY=1 COMPILER_CHECKED=0 NO_EVIDENCE_WRITTEN=1')
