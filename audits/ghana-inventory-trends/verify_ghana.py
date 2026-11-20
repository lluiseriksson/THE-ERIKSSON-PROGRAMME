"""Verify the input tables against the deposit before running the two analyses."""
from pathlib import Path
import sys,re,hashlib,json,subprocess,zipfile,io
import xml.etree.ElementTree as ET
from ghana_trends import read,analyze
from ghana_archive import run_archive,data_sheet,need

def pdf_text(pdf,lo,hi):
    return subprocess.check_output(['pdftotext','-f',str(lo),'-l',str(hi),'-layout',str(pdf),'-']).decode('utf-8')

def verify(pdf,archive):
    data=read('table97.json');anchors=read('table17.json');crt=read('crt-trends.json')
    need(hashlib.sha256(pdf.read_bytes()).hexdigest()==data['pdf_sha256'],'NID digest differs')
    text=pdf_text(pdf,263,264)
    txt=text.split('Table 97: Recalculation results, with and without LULUCF, over the time series')[-1]
    lines={int(v[0]):v for l in txt.splitlines() if len(v:=l.split())==9 and v[0].isdigit() and v[4].endswith('%') and v[8].endswith('%')}
    need(sorted(lines)==list(range(1990,2022)),'Source rows')
    for r in data['rows']:
        vs=lines[r['year']]
        need(all(vs[i]==r[k] for i,k in [(1,'previous_with'),(2,'current_with'),(5,'previous_without'),(6,'current_without')]),'Changed Table 97')
    txt=pdf_text(pdf,79,85)
    for key,label in [('with','National emissions with LULUCF'),('without','National emissions without LULUCF'),('land','3B Land'),('hwp','3D Harvested Wood Products')]:
        line,=[l for l in txt.splitlines() if l.startswith(label)]
        v=[s.replace('(','-').replace(')','').replace(',','') for s in line[len(label):].split()[:7]]
        need(list(anchors[key].values())==v,'Changed Table 17')
    raw=archive.read_bytes()
    with zipfile.ZipFile(io.BytesIO(raw)) as outer:
        book=outer.read(crt['workbook'])
        need(hashlib.sha256(book).hexdigest()==crt['workbook_sha256'],'Final book digest')
    with zipfile.ZipFile(io.BytesIO(book)) as x:
        ss=[''.join(v.itertext()) for v in ET.fromstring(x.read('xl/sharedStrings.xml'))]
        a=data_sheet(x,55,ss);d=data_sheet(x,60,ss)
        for r in crt['rows']:
            j=r['column']
            need(a[j+'8']==d[j+'8']==str(r['year']),'Year')
            for k,cell in crt['cells'].items():
                sheet=a if k.startswith('s1_') else d
                need(sheet[j+str(cell[0])]==r[k],k)
    return dict(main=analyze(data['rows'],anchors,crt['rows']),archive=run_archive(raw))

if __name__=='__main__':
    root=Path(sys.argv[1] if len(sys.argv)>1 else '/content')
    print(json.dumps(verify(root/'ghana-nid.pdf',root/'ghana-crt.zip'),indent=2,sort_keys=True))

