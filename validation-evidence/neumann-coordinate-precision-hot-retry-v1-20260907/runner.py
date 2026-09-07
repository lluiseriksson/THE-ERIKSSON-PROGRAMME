"""One bounded R2 repair on retained runtime; no bootstrap or cold seal."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tarfile
import time
import types
import urllib.request

SOURCE='249ee54287989580df0f802796937caa1e4107a0'
BASE='95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
REV='neumann-coordinate-precision-hot-retry-v1'
ROOT=Path('/content/hrpoly-neumann-coordinate-precision-diagnostic-v1')
OUT=Path('/content/'+REV+'-evidence')
ARCHIVE=Path(str(OUT)+'.tar.gz')
PARENT_HASH='5ce85f28076e99319b122dabef5949b23ed8858fc59f654091925f3254abfe04'
PINS={'NeumannCoordinateMomentumCarryDraft.lean':'4f75ddbacfd31824b63f4ebcd83be28a8e6ecb440c855fdaad7c976a17518fc4',
      'NeumannCoordinateAveragePhaseDraft.lean':'34572ae8bb05d3a2928abd172504ee201b58616e1817ca236283e4c73333d645'}
GATE_HASH='016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
RAW='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
NAMES={'carry':['neumannEntireAliasFineSymbol_coordinateReflection','neumannEntireScaledLaplacianSymbol_coordinateReflection','neumannMomentumCoordinateReflection_involutive','neumannPhysicalAliasCoordinateReflection_momentum'],
       'phase':['neumannCoordinateHalfCellPhase_ne_zero','neumannCoordinateHalfCellPhase_neg','neumannEntireAliasAverageColumn_coordinateReflection','neumannEntireAliasAverageRow_coordinateReflection','neumannEntireAliasPrecisionMatrix_coordinateReflection','neumannEntireAverageAmplitude_coordinateReflection']}
def sha(b): return hashlib.sha256(b).hexdigest()

def main():
    assert not OUT.exists() and not ARCHIVE.exists(),'NO_REEXECUTION'
    parent=Path(str(ROOT)+'-evidence.tar.gz')
    assert sha(parent.read_bytes())==PARENT_HASH,'PARENT_HASH'
    assert not Path('/proc/8249').exists(),'PARENT_STILL_RUNNING'
    OUT.mkdir(); scratch=ROOT/'tmp'/REV; scratch.mkdir(exist_ok=False)
    env=os.environ.copy(); bins=list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
    assert len(bins)==1,'TOOLCHAIN'; env['PATH']=str(bins[0].parent)+':'+env['PATH']
    records=[]; audits={}; outputs={}; status='FAIL'; error=None
    def run(stage,cmd):
        start=time.perf_counter(); log=OUT/(stage+'.log'); timed=False
        with log.open('xb') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            print('STAGE='+stage+' PID='+str(p.pid),flush=True)
            try: code=p.wait(timeout=120)
            except subprocess.TimeoutExpired:
                timed=True; os.killpg(p.pid,signal.SIGKILL); code=p.wait()
        b=log.read_bytes(); r=dict(stage=stage,command=cmd,cwd=str(ROOT),exit=code,seconds=time.perf_counter()-start,timed_out=timed,log_sha256=sha(b))
        records.append(r); t=OUT/'records.tmp'; t.write_text(json.dumps(records,sort_keys=True)+'\n'); t.replace(OUT/'records.json')
        print(b.decode(errors='replace'),flush=True); print(json.dumps(r,sort_keys=True),flush=True)
        assert code==0 and not timed,'FIRST_ERROR='+stage
        return b.decode()
    try:
        assert run('head',['git','rev-parse','HEAD']).strip()==BASE
        assert run('mathlib',['git','-C','.lake/packages/mathlib','rev-parse','HEAD']).strip()=='07642720480157414db592fa85b626dafb71355b'
        for exe in ('lean','lake'):
            assert '4.29.0-rc6' in run(exe+'_version',[exe,'--version'])
            (OUT/(exe+'-sha256.txt')).write_text(sha((bins[0].parent/exe).read_bytes())+'\n')
        run('clean_before',['git','diff','--exit-code','HEAD','--','YangMills','tmp/NeumannCoordinateMomentumCarryDraft.lean','tmp/NeumannCoordinateAveragePhaseDraft.lean','lean-toolchain','lake-manifest.json'])
        contract=json.loads(Path(str(ROOT)+'-evidence/coordinate-contract.json').read_text())
        assert contract['source']==BASE
        for name,digest in contract['outputs'].items():
            assert sha((ROOT/'.lake/build/lib/lean'/name).read_bytes())==digest,'PARENT_OUTPUT='+name
        (OUT/'parent-contract.json').write_text(json.dumps(contract,sort_keys=True)+'\n')
        gb=urllib.request.urlopen(RAW+SOURCE+'/scripts/full_green_owner_exact_axiom_gate.py',timeout=60).read()
        assert sha(gb)==GATE_HASH; (OUT/'axiom-gate.py').write_bytes(gb)
        gate=types.ModuleType('pinned_gate'); exec(compile(gb,'pinned_gate','exec'),gate.__dict__); gate.self_test()
        for name,digest in PINS.items():
            b=urllib.request.urlopen(RAW+SOURCE+'/tmp/'+name,timeout=60).read(); assert sha(b)==digest,'SOURCE='+name
            (scratch/name).write_bytes(b); (OUT/name).write_bytes(b)
        for stage,name in zip(('carry','phase'),PINS):
            op=ROOT/'.lake/build/lib/lean'/name.replace('.lean','.olean')
            assert not op.exists(),'OUTPUT_ALREADY_EXISTS'
            text=run(stage,['lake','env','lean','-o',str(op.relative_to(ROOT)),str((scratch/name).relative_to(ROOT))])
            audits[stage]=gate.exact_axioms(text,{'YangMills.RG.'+n for n in NAMES[stage]})
            b=op.read_bytes(); outputs[op.name]=sha(b); (OUT/op.name).write_bytes(b)
        run('clean_after',['git','diff','--exit-code','HEAD','--','YangMills','tmp/NeumannCoordinateMomentumCarryDraft.lean','tmp/NeumannCoordinateAveragePhaseDraft.lean','lean-toolchain','lake-manifest.json'])
        status='PASS'
    except Exception as e:
        error=repr(e); print('ERROR='+error,flush=True)
    finally:
        (OUT/'runner.py').write_bytes(Path(__file__).read_bytes())
        (OUT/'result.json').write_text(json.dumps(dict(status=status,cold_seal=False,source=SOURCE,base=BASE,revision=REV,parent_hash=PARENT_HASH,pins=PINS,gate_hash=GATE_HASH,names=NAMES,records=records,audits=audits,outputs=outputs,error=error),sort_keys=True)+'\n')
        with tarfile.open(ARCHIVE,'w:gz') as t: t.add(OUT,arcname=OUT.name)
        print('FINAL_STATUS='+status+' COLD_SEAL=0',flush=True)
        print('ARCHIVE='+str(ARCHIVE)+'\nARCHIVE_SHA256='+sha(ARCHIVE.read_bytes()),flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1',flush=True)
    return 0 if status=='PASS' else 1

if __name__=='__main__': raise SystemExit(main())
