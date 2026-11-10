import os,sys,time,json,hashlib,zipfile,subprocess,traceback,resource,urllib.request
from pathlib import Path
from datetime import datetime,timezone
SOURCE='ef39a6a2bd60aa58260d63620a47f18a1eb0c856'
INPUTS={'sharp_coexact_rank_diagnostic229.py': {'path': 'scripts/sharp_coexact_rank_diagnostic229.py', 'sha256': 'e59ef4b6311407f7f2ec98fe7328fe38de76fb9efb2f52f6814dd6415ab017fb'}, 'coexact_partition_rank_diagnostic228.py': {'path': 'scripts/coexact_partition_rank_diagnostic228.py', 'sha256': 'f6a0a5fde053b6430ba0545a88bbed3844e4fb576a175a9ab07173180f8d3b5c'}, 'sharp-coexact229-draft.txt': {'path': 'papers/flat-coarse-rank/research/2026-11-10_sharp-coexact229.txt', 'sha256': '8b8457bdacc242150492890e6b08503356a6c9328ce787501239528eb303da70'}}
if not Path('/content').is_dir():raise RuntimeError('Own ColabLinux required')
out=Path('/content/tep229-diagnostic');out.mkdir(exist_ok=False);start=time.monotonic()
report={'started_utc':datetime.now(timezone.utc).isoformat(),'source_context':'source'+SOURCE,'input_pins':{k:v['sha256'] for k,v in INPUTS.items()},'python':sys.version,'runtime':'Own ColabLinux CPU highmemory; no Windows scientific execution','compute_units_billed':None,'exits':{},'source_audit_pending':False,'scope':'Selected sharp229rank/annihilator/drift/fibre checks only; fullL16coefficient-budgetfamily is not executed.'}
try:
 for name,spec in INPUTS.items():
  b=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+spec['path'],timeout=45).read()
  if hashlib.sha256(b).hexdigest()!=spec['sha256']:raise ValueError('Frozen input '+name)
  (out/name).write_bytes(b)
 for mode,flags in [('normal',[]),('optimized',['-O'])]:
  bootstrap = ('import sys,json,hashlib,runpy; from pathlib import Path; '
      + 'sys.path.insert(0,'+repr(str(out))+'); import coexact_partition_rank_diagnostic228 as base; '
      + 'actual=Path(base.__file__).resolve(); expected=Path('+repr(str(out/'coexact_partition_rank_diagnostic228.py'))+').resolve(); '
      + 'need=lambda ok,msg: None if ok else (_ for _ in ()).throw(ValueError(msg)); '
      + 'need(actual==expected,"Imported dependency path"); '
      + 'pin=hashlib.sha256(actual.read_bytes()).hexdigest(); need(pin=='+repr(INPUTS['coexact_partition_rank_diagnostic228.py']['sha256'])+',"Imported dependency hash"); '
      + 'need(sys.flags.optimize=='+str(0 if mode=='normal' else 1)+',"Actual optimization flag"); '
      + 'Path('+repr(str(out/(mode+'.dependency.json')))+').write_text(json.dumps(dict(actual_dependency_file=str(actual),raw_sha256=pin,optimization_flag=sys.flags.optimize))); '
      + 'runpy.run_path('+repr(str(out/'sharp_coexact_rank_diagnostic229.py'))+',run_name="__main__")')
  p=subprocess.run([sys.executable,*flags,'-c',bootstrap],cwd=out,capture_output=True,timeout=300)
  (out/(mode+'.stdout')).write_bytes(p.stdout);(out/(mode+'.stderr')).write_bytes(p.stderr)
  t=out/(mode+'.exit.tmp');t.write_text(str(p.returncode)+'\n');v=int(t.read_text().strip());os.replace(t,out/(mode+'.exit'));report['exits'][mode]=v
  if v:raise RuntimeError(mode+' actual diagnostic exit '+str(v))
 same=(out/'normal.stdout').read_bytes()==(out/'optimized.stdout').read_bytes()
 if not same:raise ValueError('Normal/optimized outputs differ')
 data=json.loads((out/'normal.stdout').read_bytes())
 if data.get('completed_cases')!=21 or len(data['cases'])!=21 or data['all_partitions_of_D2n2']!=15 or data['rejected_controls']!=3 or not all(data['negative_controls'].values()):raise ValueError('Preregistered selected counts/control failures')
 report.update(status='FINITE_DIAGNOSTICS_CHECKED',normal_optimized_output_equal=True)
except Exception:
 report['status']='FAILED_PRESERVED';(out/'failure.txt').write_text(traceback.format_exc())
finally:
 report.update(finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-start,child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
 (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 manifest={'files':[{'file':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(out.iterdir()) if p.is_file()]}
 (out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
 archive=Path('/content/tep229-diagnostics.zip')
 with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(out.iterdir()):
   if p.is_file():z.write(p,p.name)
 print(json.dumps(report));print('ZIP_SHA256='+hashlib.sha256(archive.read_bytes()).hexdigest())
 if report['status']=='FAILED_PRESERVED':sys.exit(1)
