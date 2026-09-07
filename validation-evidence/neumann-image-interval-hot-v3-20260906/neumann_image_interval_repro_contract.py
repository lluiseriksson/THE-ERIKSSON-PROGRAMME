"""Verbatim Mathlib extraction for the independent image-coverage diagnostic.

This produces bytes, not compiler evidence. No source proof is changed.
"""
import hashlib

SOURCE = 'f9e6f5eb044e22424a5ed0732bc581b94d8c8b3c'
DRAFT_PATH = 'tmp/NeumannImageIntervalCoverageDraft.lean'
ORBIT_PATH = 'YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebra.lean'
NAMES = [
    'neumannOrbitFalse_periodQuotient', 'neumannOrbitTrue_periodQuotient',
    'neumannOrbitFalse_periodRemainder', 'neumannOrbitTrue_periodRemainder',
    'neumannImageIntervalFamily_injective', 'neumannImageIntervalFamily_surjective',
    'neumannImageIntervalFamily_bijective',
]


def make_repro(draft, orbit):
    d, o = draft.decode('utf-8'), orbit.decode('utf-8')
    marker = 'import YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra\n'
    assert d.startswith(marker) and d.count(marker) == 1
    d = d[len(marker):]
    start = o.index('def cmp89NeumannReflectionOrbit ')
    end = o.index('/-- The lower reflection exchanges', start)
    definitions = o[start:end]
    assert definitions.count('def cmp89NeumannReflectionOrbit ') == 1
    assert definitions.count('@[simp] theorem cmp89NeumannReflectionOrbit_') == 2
    ns = 'namespace YangMills.RG\n'
    assert d.count(ns) == 1
    d = d.replace(ns, ns + '\n' + definitions, 1)
    assert 'import YangMills.' not in d
    assert [line.removeprefix('#print axioms YangMills.RG.') for line in d.splitlines()
            if line.startswith('#print axioms YangMills.RG.')] == NAMES
    return d.encode('utf-8')


if __name__ == '__main__':
    import subprocess
    def blob(path):
        return subprocess.check_output(['git', 'cat-file', 'blob', SOURCE + ':' + path], timeout=5)
    draft, orbit = blob(DRAFT_PATH), blob(ORBIT_PATH)
    for name, data in [('draft', draft), ('orbit', orbit), ('repro', make_repro(draft, orbit))]:
        print(name + '_sha256=' + hashlib.sha256(data).hexdigest())
    print('VERBATIM_REPRO_READY names=7 COMPILER_CHECKED=0')
