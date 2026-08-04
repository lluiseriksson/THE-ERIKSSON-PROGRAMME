# OS-R pass 7 -- FRESH-CLONE VERIFICATION at 8127e5b52 (wired tree).
# Brand-new clone in /content/osrfresh (never reuses /content/osr1).
# Ladder: judges (judge_os_uniform, normal AND -O) -> module build ->
# core build (EXPECT 8481) -> full oracle with a CONTINUATION-JOINING
# axiom checker (EXPECT 3017 reports, all on the standard triple,
# 0 sorryAx) -> sha256 of the travelling files.
import hashlib, os, pathlib, re, subprocess, shutil

SHA = '8127e5b52d75116b19c172ea022e12c1cab0f8c2'
REPO = pathlib.Path('/content/osrfresh')
ENV = {**os.environ, 'PATH': '/root/.elan/bin:' + os.environ['PATH']}

def run(cmd, timeout, cwd=REPO):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout, env=ENV)
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
    subprocess.run('curl -sSf https://raw.githubusercontent.com/leanprover/elan/'
                   'master/elan-init.sh | sh -s -- -y --default-toolchain none',
                   shell=True, cwd=REPO, env=ENV)
rc, out = run(['lake', 'exe', 'cache', 'get'], 1800)
print('CACHE_EXIT', rc, flush=True)

print('=== judges: judge_os_uniform, both modes ===', flush=True)
for mode, argv in (('normal', ['python3', 'scripts/judge_os_uniform.py']),
                   ('optimized', ['python3', '-O', 'scripts/judge_os_uniform.py'])):
    rc, out = run(argv, 600)
    tail = [l for l in out.splitlines() if 'checks run' in l or 'VERDICT' in l]
    print(f'JUDGE_{mode.upper()}_EXIT', rc, '|', ' | '.join(tail), flush=True)

print('=== module + core build (EXPECT total 8481) ===', flush=True)
rc, out = run(['lake', 'build', 'YangMillsCore'], 5400)
ms = re.findall(r'\[(\d+)/(\d+)\]', out)
total = ms[-1][1] if ms else 'NONE'
done_line = [l for l in out.splitlines() if 'Build completed' in l]
print('CORE_EXIT', rc, 'TOTAL', total, '|', ' '.join(done_line), flush=True)

print('=== full oracle, continuation-joining checker ===', flush=True)
rc, out = run(['lake', 'env', 'lean', 'oracle_check.lean'], 3600)
# join wrapped reports: a report starts at a line beginning with a quote
reports = []
cur = None
for line in out.splitlines():
    if line.startswith("'"):
        if cur is not None:
            reports.append(cur)
        cur = line
    elif cur is not None:
        cur += ' ' + line.strip()
if cur is not None:
    reports.append(cur)
n_rep = sum(1 for r in reports if 'depends on axioms' in r)
n_sorry = sum(1 for r in reports if 'sorryAx' in r)
STD = re.compile(r'depends on axioms:\s*\[propext,\s*Classical\.choice,\s*Quot\.sound\]\s*$')
nonstd = [r for r in reports if 'depends on axioms' in r and not STD.search(r)]
print('ORACLE_EXIT', rc, 'REPORTS', n_rep, 'SORRYAX_REPORTS', n_sorry,
      'NONSTANDARD_JOINED', len(nonstd), flush=True)
for r in nonstd[:10]:
    print('NONSTD:', r[:200], flush=True)
for name in ['os_reconstruction_uniform_gap', 'os_reconstruction_uniform_clustering']:
    for r in reports:
        if name in r:
            print('OSR:', r[:180], flush=True)
            break

print('=== hashes of the travelling files ===', flush=True)
for f in ['YangMills/OS/OSReconstructionUniform.lean', 'YangMillsCore.lean',
          'oracle_check.lean', 'scripts/judge_os_uniform.py',
          'scripts/osr1_pass7_freshclone.py']:
    p = REPO / f
    if p.exists():
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        print(f'{h}  {p.stat().st_size:>8}  {f}', flush=True)
print('OSR1_FRESHCLONE_DONE', flush=True)
