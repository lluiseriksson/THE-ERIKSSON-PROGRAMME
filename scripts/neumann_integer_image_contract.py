"""Pinned seven-name R2 diagnostic contract; no I/O or compiler on import."""
import hashlib

SOURCE = '9bba6c7b8c6f447a8e1914acca66e5c904beb154'
REV = 'neumann-integer-image-counting-diagnostic-v1'
ROOT = '/content/hrpoly-' + REV
EVIDENCE = ROOT + '-evidence'
DRAFT = 'tmp/NeumannIntegerImageCountingKernelDraft.lean'
ORBIT = 'YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebra.lean'
BRANCH = 'YangMills/RG/BalabanCMP89NeumannReflectionBranchSum.lean'
REPRO = 'tmp/NeumannIntegerImageCountingMathlibRepro.lean'
BLOBS = {
    DRAFT: 'fc6f119ba5a57908686e21316af5d3fba89409618d19451db879e7196512dd6a',
    ORBIT: '25a68943ae80ca3dcb4dbd22f2db7e10501d7b10c021692c84870f8a1fbb843a',
    BRANCH: 'a2bc16c72a54e7baaf9389bc1f4124eb568bfbaae03150423963585a499852c0',
}
NAMES = {'YangMills.RG.' + n for n in (
    'neumannIntegerHalfCellOwner', 'neumannIntegerTranslatedOwner',
    'neumannIntegerReflectedOwner', 'neumannIntegerBlockOwner_image',
    'neumannIntegerReflectionImage_injective', 'neumannIntegerBlockOwner_image_eq_iff',
    'neumannIntegerCountingIndicator_image')}
COMMANDS = {
    'image_mathlib_repro': ['lake', 'env', 'lean', '-o', EVIDENCE + '/mathlib-repro.olean', REPRO],
    'image_prerequisites': ['lake', 'build', 'YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra'],
    'image_draft': ['lake', 'env', 'lean', '-o', EVIDENCE + '/image-draft.olean', DRAFT],
    'final_clean_source': ['git', 'diff', '--exit-code', 'HEAD', '--',
                           'YangMills', 'tmp/NeumannIntegerImageCountingKernelDraft.lean',
                           'lean-toolchain', 'lake-manifest.json'],
}
BASE_SHA = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
BASE_WRAPPER_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
BASE_RUNNER_HASH = '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def minimal_text(inputs):
    for path, digest in BLOBS.items():
        if sha(inputs[path]) != digest:
            raise ValueError('SOURCE_PIN=' + path)
    draft, orbit, branch = (inputs[p].decode('utf-8') for p in (DRAFT, ORBIT, BRANCH))

    def definition(text, name):
        start = text.index('def ' + name + ' ')
        end = text.index('\n\n@[simp]', start)
        return text[start:end]

    alias = next(line for line in branch.splitlines()
                 if line.startswith('abbrev CMP89NeumannReflectionBranch '))
    declarations = '\n\n'.join([alias, definition(orbit, 'cmp89NeumannReflectionOrbit'),
                                definition(orbit, 'cmp89NeumannReflectionImage')])
    prefix = ('import Mathlib.Data.Int.DivMod\nimport Mathlib.Data.Real.Basic\n'
              'import Mathlib.Data.Fintype.Pi\nimport Mathlib.Tactic.Linarith\n'
              'import Mathlib.Tactic.Ring\n\n'
              '/-! PRE-VALIDATION: extracted Mathlib-only repro, not a physical seal. -/\n'
              'namespace YangMills.RG\n' + declarations + '\nend YangMills.RG\n\n')
    # All seven proof statements/bodies are taken verbatim from the pinned draft.
    return (prefix + draft[draft.index('namespace YangMills.RG'):]).encode('utf-8')
