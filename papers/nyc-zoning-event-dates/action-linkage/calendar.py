rows=[["190260ZMQ","2021","2021"],["200101ZMK","2023","2023"],["200228ZMX","2022","2022"],["200232ZMQ","2022","2023"],["200246ZMQ","2021","2022"],["200296ZMK","2021","2021"],["200299ZMQ","2021","2021"],["200310ZMK","2023","2024"],["200317ZMK","2022","2022"],["200329ZMK","2021","2022"],["200335ZMK","2021","2022"],["200358ZMK","2021","2022"],["210025ZMQ","2021","2021"],["210031ZMK","2021","2022"],["210098ZMK","2021","2022"],["210119ZMK","2021","2021"],["210128ZMQ","2022","2022"],["210148ZMQ","2021","2021"],["210151ZMK","2021","2021"],["210161ZMQ","2021","2022"],["210164ZMQ","2021","2021"],["210166ZMK","2021","2021"],["210174ZMK","2022","2022"],["210177ZMK","2021","2021"],["210189ZMQ","2021","2022"],["210192ZMQ","2021","2021"],["210200ZMQ","2021","2021"],["210213ZMQ","2021","2022"],["210234ZMQ","2022","2022"],["210239ZMK","2021","2022"],["210249ZMK","2021","2021"],["210253ZMK","2021","2021"],["210276ZMK","2021","2021"],["210278ZMK","2021","2021"],["210283ZMQ","2022","2023"],["210285ZMK","2021","2022"],["210289ZMR","2021","2021"],["210299ZMK","2021","2022"],["210312ZMK","2021","2022"],["210314ZMK","2023","2023"],["210317ZMQ","2022","2023"],["210321ZMX","2021","2022"],["210332ZMK","2022","2023"],["210335ZMK","2021","2022"],["210339ZMX","2021","2021"],["210351ZMM","2021","2021"],["210361ZMR","2021","2021"],["210386ZMK","2021","2022"],["210391ZMX","2021","2022"],["210394ZMQ","2022","2022"],["210422ZMM","2021","2021"],["210462ZMK","2021","2021"],["220007ZMX","2022","2022"],["220050ZMQ","2022","2022"],["220062ZMK","2021","2021"],["220080ZMK","2024","2024"],["220111ZMK","2021","2022"],["220133ZMQ","2022","2022"],["220169ZMQ","2022","2022"],["220171ZMX","2022","2022"],["220185ZMQ","2024","2024"],["220188ZMK","2022","2022"],["220196ZMQ","2022","2022"],["220203ZMX","2022","2022"],["220220ZMM","2022","2022"],["220232ZMQ","2021","2022"],["220250ZMQ","2022","2023"],["220267ZMQ","2022","2023"],["220274ZMQ","2022","2023"],["220283ZMX","2022","2023"],["220285ZMK","2023","2023"],["220306ZMX","2022","2023"],["220312ZMK","2022","2022"],["220334ZMX","2023","2023"],["220364ZMQ","2022","2022"],["220414ZMQ","2022","2022"],["220426ZMR","2023","2023"],["220429ZMK","2022","2022"],["220438ZMK","2023","2023"],["220453ZMK","2023","2023"],["220456ZMR","2023","2023"],["220470ZMK","2022","2023"],["230001ZMK","2023","2023"],["230006ZMQ","2022","2023"],["230010ZMK","2023","2023"],["230012ZMQ","2023","2023"],["230022ZMQ","2024","2024"],["230041ZMQ","2023","2023"],["230051ZMK","2023","2024"],["230052ZMQ","2022","2023"],["230091ZMQ","2023","2024"],["230126ZMQ","2023","2024"],["230146ZMK","2023","2024"],["230206ZMM","2024","2024"],["230241ZMM","2023","2024"],["230250ZMQ","2024","2024"],["230255ZMK","2023","2024"],["230258ZMK","2024","2024"],["230276ZMQ","2024","2024"],["230289ZMK","2023","2024"],["230291ZMX","2023","2023"],["230293ZMK","2024","2024"],["230306ZMQ","2023","2024"],["230307ZMQ","2023","2024"],["230323ZMK","2023","2024"],["230337ZMK","2023","2024"],["230344ZMM","2023","2024"],["230351ZMK","2024","2024"],["230354ZMK","2024","2024"],["230356ZMK","2024","2024"],["230381ZMK","2023","2024"],["240015ZMX","2024","2024"],["240030ZMK","2023","2024"],["240072ZMK","2024","2024"],["240075ZMQ","2023","2024"],["240131ZMK","2024","2024"],["240237ZMM","2024","2024"],["240328ZMQ","2024","2024"]]
input_hashes={"sensitivity.json":"8bdc68fe7235fc15405ef654d9eac4f3d849d190b453a918da3bb2161bf9d33b","projects.json":"e8c3e164dad6b562a5168c8a1e213aaa567806b64c35e732b8e961232ea60a73"}
import json,re,zipfile,hashlib,collections
from pathlib import Path
from urllib.request import Request,urlopen
from bs4 import BeautifulSoup
h=lambda v:hashlib.sha256(v).hexdigest()
assert len(rows)==len({r[0] for r in rows})==118
schedule={};rawpages={};yearset={int(y) for _,a,b in rows for y in (a,b)}
assert yearset=={2021,2022,2023,2024}
for y in sorted(yearset):
    url='https://vote.nyc/page/election-results-summary-'+str(y)
    with urlopen(Request(url,headers={'User-Agent':'Programme research on annual municipal records'}),timeout=35) as f:data=f.read(2000001)
    assert len(data)<=2000000
    soup=BeautifulSoup(data,'html.parser')
    titles=[t for t in soup.find_all('h2') if 'GENERAL' in t.get_text(' ',strip=True).upper() and 'NOVEMBER' in t.get_text(' ',strip=True).upper()]
    assert len(titles)==1,(y,[t.get_text() for t in soup.find_all('h2')])
    title=titles[0];first=[]
    for item in title.find_all_next(['h2','tr']):
        if item.name=='h2':break
        td=item.find(['td','th'])
        if td:first.append(' '.join(td.stripped_strings))
    assert len(first)>10,(y,len(first))
    cand=[s for s in first if re.search(r'of the City Council|Council Member|City Council Member',s,re.I)]
    matches=[re.search(r'(\d+)(?:st|nd|rd|th)?\s+Council District',s,re.I) for s in cand]
    assert all(matches),(y,[s for s,m in zip(cand,matches) if not m])
    districts=sorted({int(m.group(1)) for m in matches})
    assert set(districts)<=set(range(1,52))
    rawpages[str(y)+'.html']=data
    schedule[str(y)]=dict(url=url,sha256=h(data),heading=title.get_text(' ',strip=True),rows=len(first),districts=districts)
full={y for y,r in schedule.items() if r['districts']==list(range(1,52))}
def build(rs):
    table=collections.Counter((int(a in full),int(b in full)) for _,a,b in rs)
    return {str(a)+str(b):table[a,b] for a in (0,1) for b in (0,1)}
out={'schedule':schedule,'full':sorted(full),'pairs':build(rows),'n':len(rows),'direction':'first certification / second effective map year','input_sha256':input_hashes}
arch=Path('/content/council-calendar.zip')
with zipfile.ZipFile(arch,'x',zipfile.ZIP_DEFLATED) as z:
    z.writestr('aggregate.json',json.dumps(out,indent=2))
    for k,v in rawpages.items():z.writestr(k,v)
print('archive_sha256 '+h(arch.read_bytes()))
