"""Verbatim finite-block image repro; no compiler, network or file writes."""

DRAFT = 'tmp/NeumannIntegerBlockImageAverageDraft.lean'
FINITE = 'YangMills/L0_Lattice/FiniteLattice.lean'
HALF = 'YangMills/RG/NeumannHalfCellBlockReflection.lean'
ORBIT = 'YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebra.lean'
BRANCH = 'YangMills/RG/BalabanCMP89NeumannReflectionBranchSum.lean'
INPUTS = [DRAFT, FINITE, HALF, ORBIT, BRANCH]
NAMES = ['neumannIntegerImage_fineBlockPoint',
         'sum_neumannIntegerImage_fineBlockPoint',
         'weightedSum_neumannIntegerImage_fineBlockPoint']

def fragment(text, start, end):
    assert text.count(start) == 1, 'START_COUNT=' + start
    a = text.index(start)
    b = text.find(end, a)
    assert b > a, 'MISSING_END=' + end
    return text[a:b].rstrip() + '\n'

def make_repro(files):
    t = {p: files[p].decode('utf-8') for p in INPUTS}
    finite = fragment(t[FINITE], 'abbrev FinBox ', 'theorem card_finBox')
    half = fragment(t[HALF], 'def neumannHalfCellReflection ',
                    'theorem blockSite_neumannHalfCellReflection')
    orbit = fragment(t[ORBIT], 'def cmp89NeumannReflectionOrbit ',
                     '/-- The lower reflection exchanges')
    image = fragment(t[ORBIT], 'def cmp89NeumannReflectionImage ', 'end YangMills.RG')
    branch = fragment(t[BRANCH], 'abbrev CMP89NeumannReflectionBranch ',
                      '/-- A branch carries')
    imports = ('import YangMills.RG.NeumannHalfCellBlockReflection\n'
               'import YangMills.RG.NeumannIntegerImageCountingKernel\n')
    assert t[DRAFT].startswith(imports)
    draft = t[DRAFT][len(imports):]
    result = ('import Mathlib\nnamespace YangMills\n' + finite +
              '\nend YangMills\nnamespace YangMills.RG\n' +
              orbit + branch + image + half + '\nend YangMills.RG\n' + draft)
    assert 'import YangMills.' not in result
    assert [l.removeprefix('#print axioms YangMills.RG.')
            for l in result.splitlines() if l.startswith('#print axioms ')] == NAMES
    return result.encode('utf-8')
