# OS-R pass 6 -- THE WIRING UNIT with its count predictions.
# Runs on the warm /content/osr1 clone (module file already at pass-5 green).
# A: unwired `lake build YangMillsCore`  -> T0 (resolves 8366-vs-8480).
# B: wire the import + 7 oracle endpoints (idempotent).
# C: rebuild core -> T1.  PREDICTION: T1 == T0 + 1.
# D: run the full oracle -> report count, sorryAx count, axiom-line sample.
#    PREDICTION: wired reports == unwired reports + 7 (recorded value 3010
#    at c7b870b05; the static grep at tip says 3037 lines -- ghost #26 says
#    only the RUN's count is honest, so both are printed, neither assumed).
import os, pathlib, re, subprocess

REPO = pathlib.Path('/content/osr1')
ENV = {**os.environ, 'PATH': '/root/.elan/bin:' + os.environ['PATH']}

def run(cmd, timeout):
    p = subprocess.run(cmd, cwd=REPO, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=timeout, env=ENV)
    return p.returncode, p.stdout

def lake_total(out):
    ms = re.findall(r'\[(\d+)/(\d+)\]', out)
    return ms[-1][1] if ms else 'NO_PROGRESS_LINES'

print('=== STEP A: unwired core build ===', flush=True)
rc, out = run(['lake', 'build', 'YangMillsCore'], 3600)
t0 = lake_total(out)
print('CORE_UNWIRED_EXIT', rc, 'TOTAL_T0', t0, flush=True)
print(out[-1500:], flush=True)
if rc != 0:
    raise SystemExit('unwired core build failed; stopping before wiring')

print('=== STEP B: wiring (idempotent) ===', flush=True)
core = REPO / 'YangMillsCore.lean'
txt = core.read_text(encoding='utf-8')
if 'OSReconstructionUniform' not in txt:
    txt += ('\n-- OS-R: the transported volume-uniform gap and clustering of the\n'
            '-- reconstructed (site-form) transfer operator; consumes the\n'
            '-- Dobrushin corollary verbatim (same witnesses).\n'
            'import YangMills.OS.OSReconstructionUniform\n')
    core.write_text(txt, encoding='utf-8')
oc = REPO / 'oracle_check.lean'
otxt = oc.read_text(encoding='utf-8')
ENDPOINTS = ['siteForm_qEmbed', 'transferOp_qEmbed', 'transferOp_iterate_qEmbed',
             'act_symWeighted_eq_smul_act_tilt', 'act_iterate_eq_opOf_pow',
             'os_reconstruction_uniform_gap', 'os_reconstruction_uniform_clustering']
added = 0
for name in ENDPOINTS:
    line = f'#print axioms YangMills.OS.{name}'
    if line not in otxt:
        otxt += line + '\n'
        added += 1
oc.write_text(otxt, encoding='utf-8')
print('ORACLE_LINES_ADDED', added, flush=True)

print('=== STEP C: wired core build (PREDICTION: T0 + 1) ===', flush=True)
rc, out = run(['lake', 'build', 'YangMillsCore'], 3600)
t1 = lake_total(out)
print('CORE_WIRED_EXIT', rc, 'TOTAL_T1', t1, flush=True)
print(out[-800:], flush=True)
try:
    pred = (int(t1) == int(t0) + 1)
except ValueError:
    pred = 'UNPARSED'
print('PREDICTION_CORE_PLUS_ONE', pred, flush=True)

print('=== STEP D: full oracle ===', flush=True)
rc, out = run(['lake', 'env', 'lean', 'oracle_check.lean'], 3600)
reports = len(re.findall(r'depends on axioms', out))
sorries = len(re.findall(r'sorryAx', out))
bad = [l for l in out.splitlines()
       if 'depends on axioms' in l
       and not re.search(r'\[propext, Classical\.choice, Quot\.sound\]', l)
       and not l.rstrip().endswith('depends on axioms:')]
print('ORACLE_EXIT', rc, 'REPORTS', reports, 'SORRYAX', sorries,
      'NONSTANDARD_LINES', len(bad), flush=True)
for l in bad[:10]:
    print('NONSTD:', l, flush=True)
for name in ENDPOINTS:
    for l in out.splitlines():
        if name in l:
            print('OSR:', l, flush=True)
            break
print('OSR1_WIRING_DONE', flush=True)
