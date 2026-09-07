#!/usr/bin/env python3
"""Cold gate for the physical arbitrary-residue endpoint dictionary.

Uses a new checkout with no restored project build graph. The official
verified toolchain may be shared with the retained diagnostic runtime.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


BASE = Path('/content/colab_cmp99_endpoint_reflection_chain_cold_v2.py')
BASE_URL = (
    'https://raw.githubusercontent.com/lluiseriksson/'
    'THE-ERIKSSON-PROGRAMME/882d0cd70c79390a4ae4a2318ea91958dd9e9731/'
    'scripts/colab_cmp99_endpoint_reflection_chain_cold.py'
)
BASE_SHA256 = 'c8afd717397ce8b60e20ac91eb031e60992c705dc17c059e988a5ffc80616384'
with urllib.request.urlopen(BASE_URL, timeout=60) as response:
    blob = response.read()
digest = hashlib.sha256(blob).hexdigest()
print('BASE_RUNNER_TRANSPORT_SHA256=' + digest, flush=True)
if digest != BASE_SHA256:
    raise RuntimeError('BASE_RUNNER_TRANSPORT_HASH_MISMATCH')
BASE.write_bytes(blob)
spec = importlib.util.spec_from_file_location('physical_residue_cold_base', BASE)
if spec is None or spec.loader is None:
    raise RuntimeError('BASE_RUNNER_IMPORT_FAILED')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
runner = base.runner

runner.RUNNER_REV = 'cmp99-physical-residue-endpoint-dictionary-cold-v1'
runner.SOURCE_SHA = 'c9f4b725313dd879ae3ce6e99c844ce1d2f8b968'
runner.ROOT = Path('/content/hrpoly-cmp99-physical-residue-endpoint-cold-v1')
runner.EVIDENCE = Path('/content/hrpoly-cmp99-physical-residue-endpoint-cold-v1-evidence')
runner.ARCHIVE = Path('/content/hrpoly-cmp99-physical-residue-endpoint-cold-v1-evidence.tar.gz')
runner.PATH_MANIFEST = Path('/content/hrpoly-cmp99-physical-residue-endpoint-cold-v1-paths.txt')
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionary.lean':
        '6b6e760a4af04bd0f0b6438051f7922e956f3b7142dabe464785bf8eaea9e0c7',
    'YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionaryAudit.lean':
        '8fabe6f585eaeec19d292695596ddc0b2c468d72cc304ea07e75e8d86dbbd109',
}
runner.QUEUE = [
    ('physical_residue_endpoint_dictionary_focal',
     ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionary'],
     None),
    ('physical_residue_endpoint_dictionary_audit',
     ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionaryAudit.lean'],
     frozenset({
         'YangMills.RG.cmp99SourceGeneratedFlatPhysicalResidueEndpointBase',
         'YangMills.RG.cmp99SourceGeneratedFlatPhysicalResidueEndpointBase_cast',
         'YangMills.RG.cmp89Eq251LatticeL1Length_centered_generatedPhysicalResidueEndpoint_eq',
         'YangMills.RG.cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_eq',
         'YangMills.RG.cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_le_owner',
     })),
]

if __name__ == '__main__':
    saved_unassign = None
    try:
        from google.colab import runtime
        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print(
            'RUNTIME_UNASSIGN_DEFERRED_FOR_EVIDENCE_DOWNLOAD=1', flush=True)
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            runtime.unassign = saved_unassign
