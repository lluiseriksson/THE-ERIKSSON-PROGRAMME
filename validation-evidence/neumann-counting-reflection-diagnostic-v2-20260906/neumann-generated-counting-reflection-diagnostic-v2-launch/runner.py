"""Fresh diagnostic after measured loss of the retained v1 runtime.

Only the membership proof changes. This is not a cold production seal.
The exact v1 runner is reused with explicit new source and work-directory
pins; no source archive, failed output or successful prefix is overwritten.
"""
import hashlib
import types
import urllib.request

BASE_RUNNER = '60276b1c680f93f232e80b725093f733741d5900'
BASE_HASH = 'd241e39a1b4212a9f353eaa15f7372abac76be3092c208fbda89317919ad3277'
SOURCE = '06a928178b22c42c4ecc5387461b808ee3a19dea'
REV = 'neumann-generated-counting-reflection-diagnostic-v2'
BLOBS = {
    'tmp/NeumannGeneratedCountingMassReflectionRepro.lean':
        '4af89b1e7ca169aded4bb22e395d7d6dc291f5dffba44ee0c7328444013eaa4a',
    'tmp/NeumannGeneratedCountingMassReflectionDraft.lean':
        '5f6edb3c6c7613d59d57cd943b7f9a20af23e3f2f6fe10a5643f696b0cb86fa9',
}


def main():
    url = ('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
        + BASE_RUNNER + '/scripts/colab_neumann_generated_counting_reflection_diagnostic.py')
    with urllib.request.urlopen(url,timeout=60) as response:
        payload = response.read()
    assert hashlib.sha256(payload).hexdigest() == BASE_HASH, 'BASE_RUNNER_HASH'
    module = types.ModuleType('pinned_counting_reflection_v1_runner')
    exec(compile(payload,url,'exec'),module.__dict__)
    module.SOURCE = SOURCE
    module.REV = REV
    module.BLOBS = BLOBS
    return module.main()


if __name__ == '__main__':
    raise SystemExit(main())
