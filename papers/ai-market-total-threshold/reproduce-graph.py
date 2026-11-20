import hashlib, json, zipfile, sys, subprocess
from pathlib import Path
import requests
import numpy as np
subprocess.run([sys.executable,'-m','pip','install','-q','--disable-pip-version-check','pymupdf==1.26.5'],check=True,timeout=120)
import pymupdf as fitz
blob=requests.get('https://www.nber.org/system/files/working_papers/w36003/w36003.pdf',timeout=90)
blob.raise_for_status()
assert hashlib.sha256(blob.content).hexdigest()=='ef9d3fd42db8cbcbbaf9f08108f1547af3f5c8003e495d388f0ea6ce9560bb53'
doc=fitz.open(stream=blob.content,filetype='pdf')
def pix(i):return doc[i-1].get_pixmap(matrix=fitz.Matrix(1.35,1.35),alpha=False)
# Image coordinates on the fixed primary PDF at scale 1.35.
# Lower tick centres: -0.05 at y=474 and 0.45 at y=287; allow one pixel each.
p=pix(51);rgb=np.frombuffer(p.samples,dtype=np.uint8).reshape(p.height,p.width,3).astype(int)
assert (p.width,p.height)==(827,1070)
def center(xmin,xmax,blue):
    r,g,b=np.moveaxis(rgb[310:343,xmin:xmax,:],2,0)
    mask=(b-r>45)&(r<150) if blue else (r-b>45)&(g<160)
    row=mask.sum(axis=1)
    groups=np.split(np.where(row>=3)[0],np.where(np.diff(np.where(row>=3)[0])!=1)[0]+1)
    blobs=[g for g in groups if len(g)>=2]
    assert len(blobs)==1,(row.tolist(),blobs)
    ys=blobs[0]+310
    assert row.max()>=3 and ys.max()-ys.min()<=6,(row.tolist(),ys)
    return (int(ys.min()),int(ys.max()))
from itertools import product
def interval(yr):
    candidates=[-.05+(low-y)*.5/(low-high) for low,high,y in product([473,475],[286,288],[yr[0]-1,yr[-1]+1])]
    return [min(candidates),max(candidates)]
historical=interval(center(236,247,True));baseline=interval(center(254,265,False))
assert .33<historical[0]<historical[1]<.37 and .30<baseline[0]<baseline[1]<.35
import math
data=dict(historical_graphical=historical,baseline_graphical=baseline,
    positive_calibration_required=[math.expm1(y) for y in historical],
    difference_interval=[historical[0]-baseline[1],historical[1]-baseline[0]],
    interpretation='Graphical calibration envelope in log(1+sales), not a sampling interval or underlying numerical estimate.')
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:
    z.writestr('graph.json',json.dumps(data,indent=2))
    for i in [49,51]:z.writestr(f'page-{i}.jpg',pix(i).tobytes('jpeg',jpg_quality=90))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
