#!/usr/bin/env python3
"""Bounded step-13 diagnostic, only after the physical endpoint cold PASS.

The preceding cold checkout is never modified. Reuses the earlier diagnostic
checkout and verified toolchain; records are diagnostic, not a cold seal.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import types
import urllib.request

URL = ('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
       'e62d365fe388f509a65e45a52f830b3800bc612f/'
       'scripts/colab_cmp99_physical_residue_endpoint_dictionary_hot.py')
with urllib.request.urlopen(URL, timeout=60) as response:
    blob = response.read()
digest = hashlib.sha256(blob).hexdigest()
print('BASE_RUNNER_SHA256=' + digest, flush=True)
if digest != 'dfd2cf633019ae6866e74cdbf6fe0633f4cd222d767fee4b4f55f96c05eaeff7':
    raise RuntimeError('BASE_RUNNER_HASH_MISMATCH')
runner = types.ModuleType('full_green_residue_stage_runner')
exec(compile(blob, URL, 'exec'), runner.__dict__)
runner.RUNNER_REV = 'cmp99-full-green-arbitrary-residue-hot-v1'
runner.SOURCE_SHA = 'c771ef4622e5dd62135ccb0a873ecf98a241f94f'
runner.LOG_DIR = Path('/content') / (runner.RUNNER_REV + '-logs')
PATHS = {
    'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBound.lean':
        '0ecaad27224a9d0c5d25e3ea42bed73d5f6db6fb',
    'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBoundAudit.lean':
        'cf7b4d19a26d6f53513df00fba8250c3d1d36487',
}
EXPECTED = {
    'YangMills.RG.norm_cmp89Eq246PhysicalZeroMassGreen_le_signedLatticeWeight',
    'YangMills.RG.cmp89Eq246DirectedFullSolutionSumBound_nonneg_of_window',
    'YangMills.RG.tsum_norm_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic',
    'YangMills.RG.norm_tsum_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic',
}

def main() -> None:
    cold = Path('/content/hrpoly-cmp99-physical-residue-endpoint-cold-v1-evidence')
    evidence = json.loads((cold / 'evidence.json').read_text())
    if (evidence.get('status') != 'PASS' or
        evidence.get('source_sha') != 'c9f4b725313dd879ae3ce6e99c844ce1d2f8b968'):
        raise RuntimeError('PRECEDING_COLD_PASS_REQUIRED')
    if not runner.ROOT.is_dir() or not (runner.TOOLCHAIN_BIN / 'lake').is_file():
        raise RuntimeError('RETAINED_RUNTIME_REQUIRED')
    os.environ['PATH'] = str(runner.TOOLCHAIN_BIN) + os.pathsep + os.environ['PATH']
    print('RUNNER_REV=' + runner.RUNNER_REV, flush=True)
    runner.run('fetch_source', ['git', 'fetch', '--no-tags', 'origin', runner.SOURCE_SHA])
    runner.run('checkout_source', ['git', 'checkout', '--detach', runner.SOURCE_SHA])
    if runner.output(['git', 'rev-parse', 'HEAD']) != runner.SOURCE_SHA:
        raise RuntimeError('SOURCE_HEAD_MISMATCH')
    for path, oid in PATHS.items():
        if runner.output(['git', 'rev-parse', 'HEAD:' + path]) != oid:
            raise RuntimeError('SOURCE_BLOB_MISMATCH=' + path)
        print('SOURCE_BLOB=' + path + ' OID=' + oid, flush=True)
    manifest = Path('/content/full-green-arbitrary-residue-hot-v1-paths.txt')
    manifest.write_text('\n'.join(PATHS) + '\n')
    runner.run('overlay_guard', ['python3', 'scripts/check_lean_overlay_text.py',
        '--paths-from', str(manifest), '--require-prevalidation'])
    runner.run('import_guard', ['python3', 'scripts/check_lean_import_prefix.py', *PATHS])
    runner.run('full_green_residue_focal', ['lake', 'build',
        'YangMills.RG.BalabanCMP99FullGreenArbitraryResidueBound'])
    runner.run('full_green_residue_audit', ['lake', 'env', 'lean',
        'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBoundAudit.lean'])
    output = (runner.LOG_DIR / 'full_green_residue_audit.log').read_text()
    blocks = re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", output)
    if len(blocks) != len(EXPECTED) or {name for name, _ in blocks} != EXPECTED:
        raise RuntimeError('AXIOM_DECLARATIONS_MISMATCH')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, body in blocks:
        axioms = {item.strip() for item in body.split(',') if item.strip()}
        if not axioms <= allowed:
            raise RuntimeError('UNEXPECTED_AXIOM=' + name + ':' + repr(axioms))
    print('AXIOM_GATE=PASS DECLARATIONS=4', flush=True)
    print('FINAL_STATUS=PASS HOT_DEBUG_NOT_EVIDENCE=1', flush=True)

if __name__ == '__main__':
    main()
