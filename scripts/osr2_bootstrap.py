# OS-R-2 bootstrap -- rebuild the warm working clone /content/osr1 after a
# runtime was released.  RAM guard first (a 12 GB VM OOM-killed a run once,
# ledger Add. 612), then clone at the pinned SHA, elan, cache, and a build of
# the five imports so later elaboration passes are seconds, not minutes.
import os, pathlib, re, shutil, subprocess

SHA = 'a87551fac452c602556c36acc7b362ee29b76125'
REPO = pathlib.Path('/content/osr1')
ENV = {**os.environ, 'PATH': '/root/.elan/bin:' + os.environ['PATH']}

mem = int(re.search(r'MemTotal:\s+(\d+)',
                    pathlib.Path('/proc/meminfo').read_text()).group(1))
print('MEMTOTAL_KB', mem, flush=True)
if mem < 40_000_000:
    print('OSR2_RAM_GUARD_FAIL -- this is not a high-RAM runtime', flush=True)
    raise SystemExit(65)

def run(cmd, timeout, cwd=REPO, shell=False):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout, env=ENV,
                       shell=shell)
    return p.returncode, p.stdout

if REPO.exists():
    shutil.rmtree(REPO)
rc, out = run(['git', 'clone', '-b', 'd3-closure', '--single-branch',
               'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git',
               str(REPO)], 900, cwd=pathlib.Path('/content'))
print('CLONE_EXIT', rc, flush=True)
rc, out = run(['git', 'checkout', SHA], 120)
print('CHECKOUT_EXIT', rc, flush=True)

if not (pathlib.Path.home() / '.elan/bin/lake').exists():
    rc, out = run('curl -sSf https://raw.githubusercontent.com/leanprover/elan/'
                  'master/elan-init.sh | sh -s -- -y --default-toolchain none',
                  1200, shell=True)
    print('ELAN_EXIT', rc, flush=True)
rc, out = run(['lake', 'exe', 'cache', 'get'], 2400)
print('CACHE_EXIT', rc, flush=True)

IMPORTS = ['YangMills.OS.SpatialReconstruction', 'YangMills.OS.DobrushinCorollary',
           'YangMills.OS.DobrushinTilt', 'YangMills.OS.DobrushinTransport',
           'YangMills.OS.TransferGap']
rc, out = run(['lake', 'build'] + IMPORTS, 5400)
ms = re.findall(r'\[(\d+)/(\d+)\]', out)
print('IMPORTS_EXIT', rc, 'TOTAL', (ms[-1][1] if ms else 'NONE'), flush=True)
print(out[-1200:], flush=True)
if rc != 0:
    raise SystemExit('import build failed')
print('OSR2_BOOTSTRAP_READY', flush=True)
