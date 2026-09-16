"""Check producer/reader contract alignment and the preserved real archive.
No compiler, network, pools or modifications to the original evidence.
"""
import ast
import copy
import json
from pathlib import Path
import sys
import types

sys.path.insert(0, 'scripts')
import verify_neumann_complete_fibre_promoted_cold_v2 as v
gate = v.helper(Path('scripts'), 'full_green_owner_exact_axiom_gate.py', v.GATE_HASH)
old = v.helper(Path('scripts'), 'verify_cmp99_full_green_residue_cold.py',
    '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
v.self_test(gate, old)
tree = ast.parse(Path('scripts/colab_neumann_complete_fibre_promoted_cold.py').read_text())
contracts = [n for n in ast.walk(tree) if isinstance(n, ast.Dict) and any(
    isinstance(k, ast.Constant) and k.value == 'parent_diagnostic_source' for k in n.keys)]
assert len(contracts) == 1
env = dict(SOURCE=v.SOURCE, BASE_SHA='ddf6fdc1882edddbf063389aab4d455a8ed30801',
    audit_names=v.NAMES, runner=types.SimpleNamespace(QUEUE=[(s,c,None) for s,c in v.COMMANDS.items()]))
producer_contract = eval(compile(ast.Expression(contracts[0]), '<producer contract>', 'eval'), env)
root = Path('validation-evidence/neumann-complete-fibre-original-verifier-failure-20260906')
archive = root / ('hrpoly-' + v.REV + '-evidence.tar.gz')
old.PREFIX = 'hrpoly-' + v.REV + '-evidence'
files = old.read_archive(archive, 'a156f9b7be82c3248172e7217bd83f905171e5a1ce3a2a75c10529d5600bf702')
key = 'neumann-complete-fibre-promoted-cold-contract.json'
assert json.loads(files[key]) == producer_contract, 'PRODUCER_READER_SCHEMA'
report = v.verify(files, gate, old)
for field, value in [('parent_diagnostic_source','wrong'), ('scope','regional inverse'),
                     ('project_build_cache_restored',True), ('physical_diagnostic_source','stale')]:
    bad = dict(files); contract = copy.deepcopy(producer_contract); contract[field] = value
    bad[key] = json.dumps(contract).encode()
    try: v.verify(bad, gate, old)
    except ValueError: continue
    raise AssertionError('BAD_CONTRACT_ACCEPTED=' + field)
print('V2_PRODUCER_CONTRACT=PASS REJECTED_CONTRACTS=4 ORIGINAL_ARCHIVE_UNCHANGED=1')
print(json.dumps(report, sort_keys=True))
print('NO_COMPILER_REEXECUTION=1')
