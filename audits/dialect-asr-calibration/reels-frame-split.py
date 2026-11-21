"""Count words in publicly indexed first reels; never output interview text."""
from collections import Counter
from hashlib import sha256
from html.parser import HTMLParser
import json,re,requests,xml.etree.ElementTree as ET,time
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
class Listing(HTMLParser):
    def __init__(self):super().__init__();self.ids=[]
    def handle_starttag(self,tag,attrs):
        value=dict(attrs).get('href','')
        if tag=='a' and re.fullmatch(r'[0-9]{3}[A-Z]?/',value):self.ids.append(value[:-1])
def main():
    s=requests.Session();s.headers.update({'User-Agent':'Linguistic archive calibration research; aggregate counts and hashes only'})
    s.mount('https://',HTTPAdapter(max_retries=Retry(total=2,backoff_factor=1,status_forcelist=[502,503,504],allowed_methods=['GET'])))
    root='https://www.lap.uga.edu/Projects/DASS2019/Speakers/'
    index=s.get(root,timeout=20);index.raise_for_status();lis=Listing();lis.feed(index.text)
    ids=sorted(set(lis.ids));assert len(ids)==64 and ids[:2]==['025','027']
    rows={}
    for i in ids:
        base=root+i+'/xml/'
        first=i+'_1.xml'
        reply=s.get(base+first,timeout=20)
        parts=[(base+first,reply)]
        if reply.status_code==404:
            listing=s.get(base,timeout=20);listing.raise_for_status()
            names=sorted(set(re.findall(r'href="([^"/?]+[.]xml)"',listing.text,re.I)))
            filenames=[name for name in names if re.fullmatch(re.escape(i)+r'_0?1(?:[a-z]|[-_][ab])?[.]xml',name,re.I)]
            if len(filenames)>1 and any(re.fullmatch(re.escape(i)+r'_0?1[.]xml',n,re.I) for n in filenames):raise ValueError(('Ambiguous reel split',i,filenames))
            if not filenames:
                rows[i]=dict(unresolved=True,listing=base,names=names)
                continue
            parts=[(base+n,s.get(base+n,timeout=20)) for n in filenames]
        turns=[];sources=[]
        for url,response in parts:
            response.raise_for_status();raw=response.content;doc=ET.fromstring(raw)
            if doc.tag!='Trans':raise ValueError('Expected Transcriber XML')
            turns.extend(doc.findall('.//Turn'));sources.append(dict(url=url,bytes=len(raw),sha256=sha256(raw).hexdigest()))
        if not turns or doc.tag!='Trans':raise ValueError('Unexpected format')
        clean=Counter()
        for turn in turns:
            st=' '.join(turn.itertext())
            clean['all_letter_words']+=len(re.findall(r"[^\W\d_]+(?:['’][^\W\d_]+)*",st,re.UNICODE))
            st=re.sub(r'\{[^{}]*\}',' ',st)
            words=re.findall(r"[^\W\d_]+(?:['’][^\W\d_]+)*",st,re.UNICODE)
            clean['spoken_letter_words']+=len(words)
            clean['multi_letter_words']+=sum(len(x)>1 for x in words)
        rows[i]=dict(counts=dict(clean),parts=sources,turns=len(turns))
        time.sleep(.25)
    return dict(selection='All 64 informant IDs from the UGA DASS2019 speaker index. Prospectively selected example, not the identities of the original registered six.',credit='Kretzschmar, Renwick, Lipani, Olsen, Olsen, Shi and Stanley (2019). Transcriptions of the Digital Archive of Southern Speech. Materials obtained from the University of Georgia Linguistic Atlas Project. Copying and redistribution of LAP materials are governed by its cost-of-reproduction condition. This report distributes counts, links and hashes only.',conditions='https://www.lap.uga.edu/Projects/DASS2019/readme_DASS2019.txt',rows=rows)
if __name__=='__main__':print(json.dumps(main(),sort_keys=True))
