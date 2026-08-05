# OS-R-4 pass 23 -- FRESH-CLONE VERIFICATION (the SHA below is the
# commit that registers the pass-15 wiring numbers, Addendum 624).
# Brand-new clone in /content/osr4fresh (never reuses /content/osr1).
# Ladder: judges (judge_os_uniform, normal AND -O) -> module build ->
# core build (EXPECT 8481) -> full oracle with the CONTINUATION-JOINING
# axiom checker (EXPECT the pass-13 report count, all on the standard
# triple, 0 sorryAx) -> sha256 of the travelling files.
import hashlib, os, pathlib, re, subprocess, shutil

SHA = '0a34cec208b63eaf43b9d664a9299e74127f693a'
EXPECT_CORE = 8481
EXPECT_REPORTS = 3040
REPO = pathlib.Path('/content/osr4fresh')
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

print('=== module + core build (EXPECT total', EXPECT_CORE, ') ===', flush=True)
rc, out = run(['lake', 'build', 'YangMillsCore'], 5400)
ms = re.findall(r'\[(\d+)/(\d+)\]', out)
total = ms[-1][1] if ms else 'NONE'
done_line = [l for l in out.splitlines() if 'Build completed' in l]
print('CORE_EXIT', rc, 'TOTAL', total, '|', ' '.join(done_line), flush=True)
try:
    print('PREDICTION_CORE', int(total) == EXPECT_CORE, flush=True)
except ValueError:
    print('PREDICTION_CORE UNPARSED', flush=True)

print('=== full oracle, continuation-joining checker ===', flush=True)
rc, out = run(['lake', 'env', 'lean', 'oracle_check.lean'], 3600)
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
print('PREDICTION_REPORTS', n_rep == EXPECT_REPORTS, flush=True)
for r in nonstd[:12]:
    print('NONSTD:', r[:200], flush=True)
for name in ['os_reconstruction_uniform_gap', 'os_reconstruction_measure_uniform',
             'os_reconstruction_connected_uniform', 'six_term_connected_bound',
             'inner_pow_floor', 'os_reconstruction_normalised_clustering',
             'inner_pow_floor_offdiag', 'inner_ratio_approx',
             'os_reconstruction_vacuum_state_limit']:
    for r in reports:
        if name in r:
            print('OSR:', r[:180], flush=True)
            break

print('=== hashes of the travelling files ===', flush=True)
for f in ['YangMills/OS/OSReconstructionUniform.lean', 'YangMillsCore.lean',
          'oracle_check.lean', 'scripts/judge_os_uniform.py',
          'scripts/osr4_pass23_freshclone.py']:
    p = REPO / f
    if p.exists():
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        print(f'{h}  {p.stat().st_size:>8}  {f}', flush=True)
print('OSR4_FRESHCLONE_DONE', flush=True)
