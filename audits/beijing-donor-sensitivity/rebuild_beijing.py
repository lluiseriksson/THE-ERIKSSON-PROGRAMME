"""Rebuild the fitted designs and rational certificates in an empty directory on Linux."""
from pathlib import Path
import sys,subprocess,hashlib,zipfile,json,os,shutil,io
from urllib.request import urlopen
from tempfile import TemporaryDirectory
source=Path(__file__).resolve().parent
if __name__=='__main__':
    with TemporaryDirectory() as directory:
        d=Path(directory)
        with urlopen('https://ndownloader.figshare.com/files/71702839',timeout=45) as r:raw=r.read()
        if hashlib.md5(raw).hexdigest()!='f43ce51873e24fdf2057226eb72f7077':raise ValueError('Supplement version mismatch')
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            for name,h in json.loads((source/'members.json').read_bytes()).items():
                data=z.read(name)
                if hashlib.sha256(data).hexdigest()!=h:raise ValueError(name)
                (d/Path(name).name).write_bytes(data)
        text=(d/'Beijing_analysis.R').read_text()
        (d/'impute_only.R').write_text(text[text.index('imputed_dat <- function'):text.index('# Inputs: est and var')])
        for p in [source/'donor-fit.R',*source.glob('*.py')]:shutil.copyfile(p,d/p.name)
        env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',TZ='UTC')
        subprocess.run(['Rscript','--vanilla','donor-fit.R'],cwd=d,env=env,check=True)
        for n in ['donor-radius.py','donor-observed.py','breakpoint.py','zero.py']:
            subprocess.run([sys.executable,n],cwd=d,env=env,check=True)
        def audit(path):
            return json.loads(subprocess.check_output([sys.executable,'check_beijing.py'],cwd=path,env=env))
        if audit(d)!=audit(source):raise ValueError('Rebuilt figures or witnesses differ. Compare R and linear algebra versions.')
        print('Rebuilt series and certificates agree with the archived diagnostics.')

