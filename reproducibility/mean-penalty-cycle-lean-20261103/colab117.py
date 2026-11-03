"""Own Colab CPU/high-RAM recipe117. Corrected after preserved116 compiler failure; preserve every failure."""
import base64, hashlib, json, os, pathlib, platform, re, subprocess, sys, time
import traceback, urllib.request, zipfile
from datetime import datetime, timezone

if not sys.platform.startswith("linux"):
    raise RuntimeError("Colab Linux only; no Windows build")
from google.colab import runtime

SOURCE = "e6d137d2bf21d7fdd2e2f5a25a31b01c263fdaa2"
TARGET = "YangMills.RG.MeanPenaltyCycleObstruction"
ORACLE = "YangMills/RG/MeanPenaltyCycleObstructionOracle.lean"
EXPECTED = {
    "YangMills/RG/MeanPenaltyCycleObstruction.lean": "6a2a44f11d7189ff9a98e3b8803cff253fce01e1ed7376c87e6273cf44ee48a1",
    ORACLE: "349b9bcd4a737d9801e96909cb7c1cc7d73446c058fbe9b8ddc884384de79cb6",
}
ROOT = pathlib.Path("/content/tep-own-117-mean-penalty-cycle")
if ROOT.exists():
    runtime.unassign()
    raise RuntimeError("Recover previous117; never overwrite it")
ROOT.mkdir()
OUT = ROOT / "evidence"
OUT.mkdir()
ENV = os.environ.copy()
ENV["PATH"] = str(pathlib.Path.home()/".elan/bin") + ":" + ENV["PATH"]
report = dict(run="117", source_sha=SOURCE, status="RUNNING", steps=[],
              started_utc=datetime.now(timezone.utc).isoformat(),
              general_rectangular_theorem=False, physical_embedding_verified=False,
              independent_review=False, terminal_reproduction=False)

VALIDATOR = r'''
import json, pathlib, re, sys
NAMES=['weights_admissible','energy_from_actual_weights','observedSq_eq_output',
       'normalized_mean_norm','orthogonal_mean_decomposition','kernel_square_identity',
       'kernel_coercive','witness_exact_values','witness_negative_defect',
       'fixed_penalty_coercivity_false']
PREFIX='YangMills.RG.MeanPenaltyCycleObstruction.'
PATTERN=r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def verify(raw):
    hits=list(re.finditer(PATTERN,raw))
    if len(hits)!=10: raise ValueError('exactly ten oracle readouts required')
    rows=[]
    for hit,want in zip(hits,NAMES):
        name,axs=hit.groups()
        axes=[x.strip() for x in axs.split(',') if x.strip()]
        if name!=PREFIX+want: raise ValueError('wrong or repeated endpoint')
        if len(axes)!=len(set(axes)): raise ValueError('duplicate dependency')
        if not set(axes)<= {'propext','Classical.choice','Quot.sound'}:
            raise ValueError('unapproved dependency')
        rows.append(dict(name=name,axioms=axes))
    return rows
raw=pathlib.Path(sys.argv[1]).read_text()
rows=verify(raw)
hits=list(re.finditer(PATTERN,raw))
first=hits[0]
mutations=[raw[:first.start()]+raw[first.end():],
           raw.replace(first.group(1),'Wrong.Endpoint',1),
           raw[:first.start()]+"'"+first.group(1)+"' depends on axioms: [sorryAx]"+raw[first.end():]]
rejected=0
for bad in mutations:
    if bad==raw: raise RuntimeError('mutation did not modify real oracle')
    try: verify(bad)
    except ValueError: rejected+=1
    else: raise RuntimeError('real oracle mutation accepted')
if len(rows)!=10 or rejected!=3: raise RuntimeError('explicit counters failed')
print(json.dumps(dict(status='ORACLE_VALIDATOR_PASS',accepted=10,
                     real_mutations_rejected=3,optimized=not __debug__,rows=rows),sort_keys=True))
'''


def need(ok, why):
    if not ok:
        raise ValueError(why)


def run(name, argv, cwd=None, timeout=1800):
    start = time.monotonic()
    log = OUT/(name+".log")
    with log.open("w") as f:
        proc = subprocess.run(argv, cwd=cwd, env=ENV, stdout=f,
                              stderr=subprocess.STDOUT, timeout=timeout)
    tmp = OUT/(name+".exit.tmp")
    tmp.write_text(str(proc.returncode)+"\n")
    need(tmp.read_text() == str(proc.returncode)+"\n", "real decimal sentinel")
    tmp.replace(OUT/(name+".exit.txt"))
    step = dict(name=name,exit_code=proc.returncode,seconds=round(time.monotonic()-start,3))
    report["steps"].append(step)
    print(json.dumps(step),flush=True)
    need(proc.returncode == 0, name+" failed: "+log.read_text(errors="replace")[-5000:])
    return log


try:
    need(os.environ.get("COLAB_GPU", "0") in ["0", ""], "CPU allocation required")
    if not (pathlib.Path.home()/".elan/bin/elan").exists():
        installer=OUT/"elan-init.sh"
        urllib.request.urlretrieve("https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh",installer)
        run("install_elan",["bash",str(installer),"-y","--default-toolchain","none"],timeout=600)
    validator=OUT/"oracle-validator.py"
    validator.write_text(VALIDATOR)
    products=[]
    for label in ["fresh_a","fresh_b"]:
        clone=ROOT/label
        run(label+"_init",["git","init",str(clone)],timeout=120)
        run(label+"_remote",["git","remote","add","origin",
                             "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"],clone,120)
        for key,value in [("core.autocrlf","false"),("core.sparseCheckout","true"),
                          ("remote.origin.promisor","true"),("remote.origin.partialclonefilter","blob:none")]:
            run(label+"_config_"+key,["git","config",key,value],clone,120)
        paths=list(EXPECTED)+["lakefile.lean","lake-manifest.json","lean-toolchain"]
        (clone/".git/info/sparse-checkout").write_text("\n".join("/"+p for p in paths)+"\n")
        run(label+"_fetch",["git","fetch","--depth=1","--filter=blob:none","origin",SOURCE],clone,240)
        run(label+"_checkout",["git","checkout","--detach","FETCH_HEAD"],clone,240)
        sha=run(label+"_source",["git","rev-parse","HEAD"],clone,120).read_text().strip()
        need(sha==SOURCE,"wrong immutable source")
        for path,want in EXPECTED.items():
            data=(clone/path).read_bytes()
            need(hashlib.sha256(data).hexdigest()==want,"Lean source bytes "+path)
            dest=OUT/"source"/path
            dest.parent.mkdir(parents=True,exist_ok=True)
            if dest.exists(): need(dest.read_bytes()==data,"fresh source mismatch")
            else: dest.write_bytes(data)
        need((clone/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.29.0-rc6","toolchain pin")
        manifest=json.loads((clone/"lake-manifest.json").read_text())
        pins=[p["rev"] for p in manifest["packages"] if p["name"]=="mathlib"]
        need(pins==["07642720480157414db592fa85b626dafb71355b"],"Mathlib manifest pin")
        run(label+"_lean_version",["lean","--version"],clone,600)
        run(label+"_cache_get",["lake","exe","cache","get"],clone,1800)
        run(label+"_build",["lake","build",TARGET],clone,900)
        oracle=run(label+"_oracle",["lake","env","lean",ORACLE],clone,300)
        rows=[]
        for mode,flags in [("normal",[]),("optimized",["-O"])]:
            result=run(label+"_validator_"+mode,[sys.executable]+flags+[str(validator),str(oracle)],clone,120)
            row=json.loads(result.read_text())
            need(row["status"]=="ORACLE_VALIDATOR_PASS" and row["accepted"]==10
                 and row["real_mutations_rejected"]==3,"validator counters")
            need(row["optimized"]==(mode=="optimized"),"actual validator mode")
            rows.append(row["rows"])
        need(rows[0]==rows[1],"normal/optimized oracle mismatch")
        olean=clone/".lake/build/lib/lean/YangMills/RG/MeanPenaltyCycleObstruction.olean"
        need(olean.is_file(),"missing actual built olean")
        products.append(dict(clone=label,olean_sha256=hashlib.sha256(olean.read_bytes()).hexdigest(),
                             oracle_sha256=hashlib.sha256(oracle.read_bytes()).hexdigest(),rows=rows[0]))
    need(len(products)==2 and products[0]["olean_sha256"]==products[1]["olean_sha256"]
         and products[0]["oracle_sha256"]==products[1]["oracle_sha256"]
         and products[0]["rows"]==products[1]["rows"],"two fresh build/oracle outputs differ")
    report.update(status="FOCAL_LEAN_PAIRED_ORACLE_PASS",products=products,
                  terminal_reproduction=True,accepted_each=10,validator_mutations_rejected_each=3,
                  new_lean_run=True,scope="FINITE_FOUR_CYCLE_ONLY")
except BaseException as exc:
    report.update(status="FAIL",error=repr(exc))
    (OUT/"exception.txt").write_text(traceback.format_exc())
finally:
    report["finished_utc"]=datetime.now(timezone.utc).isoformat()
    report["colab_gpu_environment"]=os.environ.get("COLAB_GPU","unset")
    (OUT/"report.json").write_text(json.dumps(report,sort_keys=True,indent=2))
    (OUT/"recipe117.py").write_bytes(pathlib.Path(__file__).read_bytes())
    (OUT/"python-platform.txt").write_text(sys.version+"\n"+platform.platform())
    manifest={str(p.relative_to(OUT)):hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(OUT.rglob("*")) if p.is_file()}
    (OUT/"manifest.json").write_text(json.dumps(manifest,sort_keys=True,indent=2))
    bundle=ROOT/"lean117.zip"
    with zipfile.ZipFile(bundle,"w",zipfile.ZIP_DEFLATED) as z:
        for p in sorted(OUT.rglob("*")):
            if p.is_file(): z.write(p,str(p.relative_to(OUT)))
    print("FINAL_REPORT="+json.dumps(report,sort_keys=True),flush=True)
    print("BUNDLE_SHA256="+hashlib.sha256(bundle.read_bytes()).hexdigest(),flush=True)
    print("EVIDENCE_BASE64_BEGIN="+base64.b64encode(bundle.read_bytes()).decode()+"=EVIDENCE_BASE64_END",flush=True)
    print("Releasing this own CPU runtime.",flush=True)
    runtime.unassign()
