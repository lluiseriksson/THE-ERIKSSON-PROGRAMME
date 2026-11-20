from pathlib import Path
import hashlib,json,subprocess,shutil,sys
from urllib.request import Request,urlopen
sources={'old':('https://arxiv.org/pdf/2509.17418v1','5856960fbe1f0d9d4650ebd85aaf88efecaa7b7627060eeaf1f87e4baa754401'),'new':('https://aclanthology.org/2026.emnlp-main.845.pdf','87777bb7ac08ff0acb4038140cecca55f4e4cfcfa737a9da3349bcb5d5272a3b')}
if not shutil.which('pdftotext'):
    subprocess.run(['apt-get','-qq','update'],check=True,stdout=sys.stderr)
    subprocess.run(['apt-get','-qq','install','-y','poppler-utils'],check=True,stdout=sys.stderr)
out={}
for key,(url,pin) in sources.items():
    pdf=urlopen(Request(url,headers={'User-Agent':'scholarly table audit'}),timeout=35).read()
    if hashlib.sha256(pdf).hexdigest()!=pin:raise ValueError('Source changed: '+key)
    path=Path(key+'.pdf');path.write_bytes(pdf)
    for page in (5,7):
        label=key+str(page)
        text=subprocess.check_output(['pdftotext','-f',str(page),'-l',str(page),'-layout',str(path),'-']).decode()
        out[label]=text
        subprocess.run(['pdftoppm','-f',str(page),'-l',str(page),'-scale-to','1500','-jpeg','-singlefile',str(path),label],check=True)
print(json.dumps(out))