# OS-R-4 pass 22 -- THE WIRING UNIT for the pass-14 module (six-term).
# Predictions REGISTERED in the ledger addendum of the banking commit,
# BEFORE this unit runs:
#   1. core total == 8481 EXACT (43213 -> 54745 B, no module added),
#   2. oracle RUN reports == 3040 EXACT (3035 + 5 new lines),
#   3. sorryAx == 0, all five new endpoints on the standard triple.
# Runs on the warm /content/osr1 clone: fetch + checkout -f the banked
# tree, sha256 gate, build, oracle.
import hashlib, os, pathlib, re, subprocess

SHA = '6ff9074b3bb286f5775e3936b46f621549a97f45'
MODULE_SHA256 = 'ec19ffa75cd4ab443c153e3e320dc3003f3c222e451d73b5f96fde489265334b'
MODULE_SIZE = 54745
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
nonstd = [r for r in reports if 'depends on axioms' in r and not STD.search(r)]
print('ORACLE_EXIT', rc, 'REPORTS', n_rep, 'SORRYAX_REPORTS', n_sorry,
      'NONSTANDARD_JOINED', len(nonstd), flush=True)
print('PREDICTION_ORACLE_3040', n_rep == 3040, flush=True)
print('PREDICTION_SORRYAX_0', n_sorry == 0, flush=True)
for name in ['abs_sub_le_add_abs', 'inner_ratio_approx', 'exists_cone_constant', 'inner_pow_floor_offdiag', 'os_reconstruction_vacuum_state_limit']:
    hit = next((r for r in reports if name in r), None)
    print('OSR2:', (hit[:170] if hit else f'{name} MISSING'), flush=True)
print('OSR4_WIRING22_DONE', flush=True)
