# OS-R-2 pass 11 -- THE WIRING UNIT for the pass-10 module.
# Predictions were REGISTERED in ledger Addendum 621 (commit 3b0dfa9e8)
# BEFORE this unit runs:
#   1. core total == 8481 EXACT (file grew, no module added),
#   2. oracle RUN reports == 3026 EXACT (3017 + 9 new lines),
#   3. sorryAx == 0, every joined report on the standard triple.
# Runs on the warm /content/osr1 clone: fetch + checkout -f the banked
# tree, sha256 gate on the travelling files, build, oracle.
import hashlib, os, pathlib, re, subprocess

SHA = '3b0dfa9e81835106b6d43a1d582b8c12dcb8f36b'
MODULE_SHA256 = 'd9919e256ae59ac9189e397e5abf1249cfaca3284efa8f1a9307f86a27bac149'
MODULE_SIZE = 20428
REPO = pathlib.Path('/content/osr1')
ENV = {**os.environ, 'PATH': '/root/.elan/bin:' + os.environ['PATH']}

def run(cmd, timeout):
    p = subprocess.run(cmd, cwd=REPO, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout, env=ENV)
    return p.returncode, p.stdout

print('=== STEP A: fetch + checkout the banked tree ===', flush=True)
rc, out = run(['git', 'fetch', 'origin', 'd3-closure'], 300)
print('FETCH_EXIT', rc, flush=True)
rc, out = run(['git', 'checkout', '-f', SHA], 120)
print('CHECKOUT_EXIT', rc, flush=True)

print('=== STEP B: sha256 gate on the travelling files ===', flush=True)
mod = REPO / 'YangMills/OS/OSReconstructionUniform.lean'
h = hashlib.sha256(mod.read_bytes()).hexdigest()
sz = mod.stat().st_size
print('MODULE', sz, h, flush=True)
if h != MODULE_SHA256 or sz != MODULE_SIZE:
    raise SystemExit('MODULE HASH GATE FAILED -- stopping before any build')
for f in ['YangMillsCore.lean', 'oracle_check.lean']:
    p = REPO / f
    print(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_size, f,
          flush=True)
n_static = sum(1 for l in (REPO / 'oracle_check.lean').read_text(
    encoding='utf-8').splitlines() if l.startswith('#print axioms'))
print('ORACLE_STATIC_LINES', n_static, flush=True)

print('=== STEP C: core build (PREDICTION: total == 8481) ===', flush=True)
rc, out = run(['lake', 'build', 'YangMillsCore'], 5400)
ms = re.findall(r'\[(\d+)/(\d+)\]', out)
total = ms[-1][1] if ms else 'NO_PROGRESS_LINES'
done = [l for l in out.splitlines() if 'Build completed' in l]
print('CORE_EXIT', rc, 'TOTAL', total, '|', ' '.join(done), flush=True)
try:
    print('PREDICTION_CORE_8481', int(total) == 8481, flush=True)
except ValueError:
    print('PREDICTION_CORE_8481 UNPARSED', flush=True)
if rc != 0:
    raise SystemExit('core build failed; stopping before the oracle')

print('=== STEP D: full oracle, continuation-joining checker ===', flush=True)
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
SUBSET = re.compile(r'depends on axioms:\s*\[[^\]]*\]\s*$')
nonstd = [r for r in reports if 'depends on axioms' in r and not STD.search(r)]
print('ORACLE_EXIT', rc, 'REPORTS', n_rep, 'SORRYAX_REPORTS', n_sorry,
      'NONSTANDARD_JOINED', len(nonstd), flush=True)
print('PREDICTION_ORACLE_3026', n_rep == 3026, flush=True)
print('PREDICTION_SORRYAX_0', n_sorry == 0, flush=True)
for r in nonstd[:12]:
    print('NONSTD:', r[:200], flush=True)
NEW = ['act_smul_fun', 'act_iterate_smul_fun',
       'act_symWeighted_iterate_eq_smul_tilt', 'gibbsPathSum_eq_inner_pow',
       'gibbsPartition_eq_inner_pow', 'norm_sub_inner_smul_le',
       'pow_apply_norm_le', 'mixed_connCorr_bound',
       'os_reconstruction_measure_uniform']
for name in NEW:
    hit = next((r for r in reports if name in r), None)
    print('OSR2:', (hit[:170] if hit else f'{name} MISSING'), flush=True)
print('OSR2_WIRING_DONE', flush=True)
