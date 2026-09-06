"""Actual producer AST vs independent reader and six source audit names.
Synthetic metadata only; no Lean, network, or claimed compiler evidence.
"""
import ast
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

sys.path.insert(0, 'scripts')
import verify_neumann_mass_offsets_promoted_cold as v

def blob(path):
    return subprocess.check_output(['git', 'cat-file', 'blob', v.SOURCE + ':' + path], timeout=5)

def module(path, digest):
    data = blob(path)
    assert hashlib.sha256(data).hexdigest() == digest, path
    m = types.ModuleType(path)
    exec(compile(data, path, 'exec'), m.__dict__)
    return m

gate = module('scripts/full_green_owner_exact_axiom_gate.py', v.GATE_HASH)
old = module('scripts/verify_cmp99_full_green_residue_cold.py',
    '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')

tree = ast.parse(Path('scripts/colab_neumann_mass_offsets_promoted_cold.py').read_text())
main = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'main')
assigns = [n for n in main.body if isinstance(n, ast.Assign)]
producer_names = next(ast.literal_eval(n.value) for n in assigns
    if isinstance(n.targets[0], ast.Name) and n.targets[0].id == 'audit_names' and isinstance(n.value, ast.Dict))
producer_blobs = next(ast.literal_eval(n.value) for n in assigns
    if isinstance(n.targets[0], ast.Attribute) and n.targets[0].attr == 'SOURCE_BLOBS')
env = dict(SOURCE=v.SOURCE, BASE_SHA='ddf6fdc1882edddbf063389aab4d455a8ed30801',
    audit_names={s: frozenset(names) for s,names in producer_names.items()})
q = next(n.value for n in assigns if isinstance(n.targets[0], ast.Attribute) and n.targets[0].attr == 'QUEUE')
queue = eval(compile(ast.Expression(q), '<actual producer queue>', 'eval'), env)
env['runner'] = types.SimpleNamespace(QUEUE=queue)
contracts = [n for n in ast.walk(tree) if isinstance(n, ast.Dict) and any(
    isinstance(k, ast.Constant) and k.value == 'parent_diagnostic_source' for k in n.keys)]
assert len(contracts) == 1
producer_contract = eval(compile(ast.Expression(contracts[0]), '<actual producer contract>', 'eval'), env)
assert producer_blobs == v.BLOBS
assert {s:set(n) for s,n in producer_names.items()} == v.NAMES
assert {s:cmd for s,cmd,_ in queue} == v.COMMANDS
for path,digest in producer_blobs.items():
    assert hashlib.sha256(blob(path)).hexdigest() == digest, path
audit = blob('YangMills/RG/NeumannGeneratedMassCompleteOffsetsAudit.lean').decode()
names = ['YangMills.RG.' + l.removeprefix('#print axioms ') for l in audit.splitlines()
    if l.startswith('#print axioms ')]
assert len(names) == len(set(names)) == 6
assert set(names) == set.union(*v.NAMES.values())

# Capture the valid fixture only, then replace its contract by the independently
# evaluated producer AST. A reader-generated self-fixture alone is insufficient.
captured = []
original = v.verify
def capture(files, gate_arg, old_arg):
    result = original(files, gate_arg, old_arg)
    captured.append(copy.deepcopy(files))
    return result
v.verify = capture
v.self_test(gate, old)
v.verify = original
files = captured[0]
key = 'neumann-mass-offsets-promoted-cold-contract.json'
assert json.loads(files[key]) == producer_contract, 'ACTUAL_PRODUCER_READER_CONTRACT'
files[key] = json.dumps(producer_contract).encode()
v.verify(files, gate, old)
for field,value in [('parent_diagnostic_source','wrong'),('scope','regional inverse'),
                    ('project_build_cache_restored',True),('physical_diagnostic_source','stale')]:
    bad=copy.deepcopy(files)
    contract=copy.deepcopy(producer_contract)
    contract[field]=value
    bad[key]=json.dumps(contract).encode()
    try: v.verify(bad,gate,old)
    except ValueError: continue
    raise AssertionError('BAD_CONTRACT_ACCEPTED='+field)
print('MASS_OFFSETS_COLD_PREPARATION=PASS ACTUAL_CONTRACT=1 SOURCE_BLOBS=2 AUDIT_NAMES=6')
print('ADDITIONAL_CONTRACT_REJECTIONS=4 SYNTHETIC_ONLY COMPILER_CHECKED=0')
