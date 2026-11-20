"""Minimax fixed-task binary pilot for two specified public EvalPerf target regimes."""
from fractions import Fraction as F
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json,base64
DATA=json.loads(base64.b64decode('eyJnYXBzIjogWyI3OTcxMjY2NTc1ODU5NDI0NzQ4ODMzOTQ0NzQ0ODk0NzMxNDIzODYwMjE4MTMzNTk2MDM2MTc5NDU3MTI5NTI0ODQ4MzM5MjgzNDcxNDY0MTYwMjg4NDk0Nzg2ODk2MjU3NDM5MTE3NzcwMjY4MTUxNjc2NTMzNzg0NzgyMjUxODcwNzg3Mzk1MDA5NDY2MjE2ODAzMjk1MTMyNjg2OTgwMDExODIxNzc3OTAxMTQwNDAyNDg4ODAxODQxODc3MTA3MjE1OTA3Mzk2NDIxNDIzMTc2MjM1MDUzNzM4NDU2MDA1Mjg1MTgzMjAyOTA4ODAwODIyMTkzMjU1NjAwMzM4MzE5OTU1MDM5MjQ1NTU2MzA5NTA4NjA3ODY3OTkvMTI2OTk2MzUwOTI2MDk2NTUyMDc1MTk3NDc3Nzg1OTk2MjU0NTAwMTA2OTkxMDI1MDE2MDE0NDEwMDc2ODY3MDcyMjMxMzE0NTI3MzMxOTU1NjIzNDQ4MzcwNDM2NjA3MTMxOTc0NzEzMTc3NTE4OTI0MTUyMDA0MTIxMDQ5MDE0NzQwOTUwMTEwNzA0MzYzOTQ2MTI5NjUzMzM5OTc3MzM1NDk2NjQ2NjU5ODYyNTYyOTU1ODIyNzk1NjI5NTAxMzQyNzczNDM3NTAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAiLCAiOTI3NjQ1MDEzNTM4MjQxMjQyMzY3ODE2NzEzMTExMjk2NjY3Njg0NjM2NDY5ODM0OTA0MTcyMDgxMTQ3ODY0MjcxMjg3NTI0NDM3MzgyODg4MTE4MTIzODU5MDQ3NDcxNTY1MDM2NTc0NDI5NDI2ODAxMzkyNDMxMTYxMzYwNjUzNTM0Nzg2NTQxODc1NjI1NTUyMDM1NDA0MjM2NjgyMDYxNDAxMjQ1ODU2ODQ1MDk0ODgzNjk5NzgyNTEwNDk1NjY0MTI3ODA1Njk5ODg3NjA0MTEzNjMyNTgwNDUzODgzMjI0MTc3ODMyNDY3NzMwODEyNDI5NDIxMzEwNjcyODc2NTQ3MDE1ODYyNTc5MDEzNzY2MS8yNTIzNTA2NzQxNzAwNTc3MTc4MjUwNzExNjkyMTcwNjY0NzQ0MzU3MzQwMjc3NDY1MzU2NTI5MzQ4MjEwMzE4MTM0NzgyODA0NzA3MTc1MTYyMzE3NzQ0NjMxMTkzNzI3MTI1MjgwNDIzNTgyNTY4NzE1ODIwOTIxOTc1MDg1ODEzNzUwMTA2MjE2ODIwMzAyODI5NDU5Nzc2MjcyNDUxMzIxMjQ0MDA1ODM5NjE2ODc1MTY0MjEwNzk2MzU2MjAxMTcxODc1MDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAiXSwgInNvdXJjZSI6ICI3N2Y1ZjMxNGExOTg0YWEwNTY5MDc3NWNiMmZiY2JmOTc1OWJlMGQ2IiwgInRhcmdldHMiOiBbIm1ldGEtbGxhbWEtLUxsYW1hLTMuMS04Qi1JbnN0cnVjdCIsICJtZXRhLWxsYW1hLS1NZXRhLUxsYW1hLTMtOEItSW5zdHJ1Y3QiXSwgImNvdW50cyI6IHsiSHVtYW5FdmFsLzAiOiBbNzQsIDM3XSwgIkh1bWFuRXZhbC8xMTMiOiBbMTksIDBdLCAiSHVtYW5FdmFsLzExOSI6IFsxNSwgMl0sICJIdW1hbkV2YWwvMTIwIjogWzEsIDVdLCAiSHVtYW5FdmFsLzEyMSI6IFs5MywgNDFdLCAiSHVtYW5FdmFsLzE0OSI6IFs1MiwgMTZdLCAiSHVtYW5FdmFsLzE2IjogWzk0LCA5OV0sICJIdW1hbkV2YWwvMjAiOiBbNzQsIDEzXSwgIkh1bWFuRXZhbC8yNCI6IFs5MCwgNzldLCAiSHVtYW5FdmFsLzI2IjogWzEsIDBdLCAiSHVtYW5FdmFsLzMxIjogWzk5LCA3Ml0sICJIdW1hbkV2YWwvMzMiOiBbNiwgMl0sICJIdW1hbkV2YWwvMzQiOiBbMTAwLCAxMDBdLCAiSHVtYW5FdmFsLzM2IjogWzgwLCA1Ml0sICJIdW1hbkV2YWwvMzciOiBbNDAsIDRdLCAiSHVtYW5FdmFsLzQiOiBbOTUsIDM1XSwgIkh1bWFuRXZhbC80OSI6IFs1NSwgNjBdLCAiSHVtYW5FdmFsLzUxIjogWzk4LCA1NV0sICJIdW1hbkV2YWwvNTQiOiBbNDAsIDVdLCAiSHVtYW5FdmFsLzU4IjogWzk5LCA0Ml0sICJIdW1hbkV2YWwvNTkiOiBbNzMsIDEyXSwgIkh1bWFuRXZhbC82NCI6IFs5LCAwXSwgIkh1bWFuRXZhbC83NCI6IFs5OCwgOF0sICJIdW1hbkV2YWwvODUiOiBbOTYsIDY5XSwgIkh1bWFuRXZhbC84NiI6IFs5LCA2XSwgIkh1bWFuRXZhbC84NyI6IFs1NSwgMF0sICJIdW1hbkV2YWwvODkiOiBbNjMsIDY5XSwgIkh1bWFuRXZhbC85IjogWzc2LCAzMl0sICJIdW1hbkV2YWwvOTAiOiBbNzUsIDQ2XSwgIk1icHAvMTA2IjogWzg3LCA5Ml0sICJNYnBwLzEwOCI6IFsyOCwgOV0sICJNYnBwLzExIjogWzM3LCAwXSwgIk1icHAvMTExIjogWzgzLCAyMl0sICJNYnBwLzEyIjogWzg5LCAyOF0sICJNYnBwLzEyMyI6IFsxLCAwXSwgIk1icHAvMTI4IjogWzk2LCA4Nl0sICJNYnBwLzEyOSI6IFsyNiwgMl0sICJNYnBwLzEzMCI6IFs4MSwgNjddLCAiTWJwcC8xMzciOiBbNSwgMV0sICJNYnBwLzE0MCI6IFs5NiwgNjhdLCAiTWJwcC8xNDEiOiBbNDYsIDFdLCAiTWJwcC8xNiI6IFsxOSwgNV0sICJNYnBwLzE2NiI6IFs3NCwgNTFdLCAiTWJwcC8xNzAiOiBbMzAsIDc5XSwgIk1icHAvMTkiOiBbOTUsIDE3XSwgIk1icHAvMjI2IjogWzk2LCA3N10sICJNYnBwLzIzMCI6IFsxMDAsIDEwMF0sICJNYnBwLzIzOSI6IFsxLCAwXSwgIk1icHAvMjQwIjogWzIzLCAyXSwgIk1icHAvMjUxIjogWzEwLCAxXSwgIk1icHAvMjU2IjogWzM2LCAzNF0sICJNYnBwLzI2NSI6IFsyMCwgMF0sICJNYnBwLzI4MSI6IFsxMDAsIDEwMF0sICJNYnBwLzI5NiI6IFs1MiwgNzhdLCAiTWJwcC8zIjogWzEwMCwgNzhdLCAiTWJwcC8zMDgiOiBbNzYsIDEyXSwgIk1icHAvMzkyIjogWzIxLCAyXSwgIk1icHAvMzk1IjogWzEwMCwgMTAwXSwgIk1icHAvNCI6IFs4NCwgODddLCAiTWJwcC80MDUiOiBbOTksIDc2XSwgIk1icHAvNDE0IjogWzEwMCwgMTBdLCAiTWJwcC80MjEiOiBbOTMsIDkwXSwgIk1icHAvNDI0IjogWzk5LCA5OV0sICJNYnBwLzQyNSI6IFs5OCwgNzZdLCAiTWJwcC80MjgiOiBbOTksIDEwMF0sICJNYnBwLzQzMyI6IFs2NiwgMTddLCAiTWJwcC80MzciOiBbMTQsIDFdLCAiTWJwcC80NDAiOiBbMSwgMF0sICJNYnBwLzQ0NiI6IFszNywgMTBdLCAiTWJwcC80NTEiOiBbOTMsIDkxXSwgIk1icHAvNDU2IjogWzEwMCwgOTZdLCAiTWJwcC80NjAiOiBbOTAsIDk5XSwgIk1icHAvNDc0IjogWzk5LCA5OF0sICJNYnBwLzQ3NiI6IFsxMDAsIDI1XSwgIk1icHAvNDc3IjogWzcyLCA5N10sICJNYnBwLzU2MyI6IFsyOCwgMTRdLCAiTWJwcC81NzIiOiBbMywgNV0sICJNYnBwLzU3OCI6IFs5MywgNzhdLCAiTWJwcC81ODYiOiBbMzcsIDU5XSwgIk1icHAvNTg3IjogWzAsIDFdLCAiTWJwcC81ODgiOiBbMTAwLCAxMDBdLCAiTWJwcC81OTIiOiBbMSwgMF0sICJNYnBwLzU5NyI6IFs2NywgMTNdLCAiTWJwcC82MDQiOiBbNzcsIDEwXSwgIk1icHAvNjEwIjogWzQ1LCAzMV0sICJNYnBwLzYxMSI6IFs4LCAyM10sICJNYnBwLzYyIjogWzk5LCA3OF0sICJNYnBwLzYzMSI6IFsyLCA0XSwgIk1icHAvNjMyIjogWzk5LCAxNV0sICJNYnBwLzYzMyI6IFsxLCAwXSwgIk1icHAvNjQ0IjogWzg5LCA5OF0sICJNYnBwLzcyMCI6IFs4MywgOTFdLCAiTWJwcC83MjUiOiBbNDIsIDIwXSwgIk1icHAvNzMyIjogWzczLCA4OF0sICJNYnBwLzc0MCI6IFs4NiwgMzRdLCAiTWJwcC83NDQiOiBbODQsIDk4XSwgIk1icHAvNzUiOiBbOTUsIDgxXSwgIk1icHAvNzUwIjogWzk5LCA5OV0sICJNYnBwLzc1MyI6IFs5NCwgODRdLCAiTWJwcC83NTQiOiBbNTEsIDEyXSwgIk1icHAvNzU1IjogWzQwLCAyNV0sICJNYnBwLzc1NyI6IFs0MywgMzJdLCAiTWJwcC83NTgiOiBbODAsIDFdLCAiTWJwcC83NjAiOiBbOTksIDM5XSwgIk1icHAvNzY0IjogWzY0LCAzMF0sICJNYnBwLzc2NiI6IFs5OSwgNDVdLCAiTWJwcC83NzUiOiBbOTIsIDE3XSwgIk1icHAvNzc3IjogWzEwLCAzOF0sICJNYnBwLzc4MSI6IFs4OSwgOThdLCAiTWJwcC84MDAiOiBbOTksIDkyXSwgIk1icHAvODA1IjogWzk3LCA3NV0sICJNYnBwLzgwOCI6IFs5NSwgOTVdLCAiTWJwcC84OCI6IFs4OSwgNThdLCAiTWJwcC85IjogWzMwLCAxN10sICJNYnBwLzkwIjogWzgxLCAxMF0sICJNYnBwLzk0IjogWzg4LCAyOV0sICJNYnBwLzk2IjogWzkzLCAxMDBdLCAiTWJwcC85NyI6IFs5OCwgNzRdfX0='))
def solution(a,b,pa,pb):
    # x,y are probabilities of choosing easier-first after a miss/hit.
    u=a*(1-pa)+b*(1-pb)
    v=a*pa+b*pb
    points={(F(x),F(y)) for x in (0,1) for y in (0,1)}
    for edge in (F(0),F(1)):
        if u:points.add(((a-v*edge)/u,edge))
        if v:points.add((edge,(a-u*edge)/v))
    def risks(x,y):
        return a*(1-(1-pa)*x-pa*y),b*((1-pb)*x+pb*y)
    choices=[(max(risks(x,y)),x,y,*risks(x,y)) for x,y in points if 0<=x<=1 and 0<=y<=1]
    best=min(choices)
    if best[0] < a*b/(a+b)*(1-abs(pa-pb)):raise ValueError('Information bound')
    return best
def main():
    a,b=map(F,DATA['gaps'])
    costs={}
    for task,(ca,cb) in DATA['counts'].items():
        sol=solution(a,b,F(ca,100),F(cb,100))
        costs[task]=[str(x) for x in sol]
    best=min(F(row[0]) for row in costs.values())
    for t in (F(0),F(1,7),F(1)):
        if solution(a,b,t,t)[0]!=a*b/(a+b):raise ValueError('No-information pilot')
    if solution(a,b,F(1),F(0))[0]!=0 or solution(a,b,F(0),F(1))[0]!=0:raise ValueError('Perfect discriminator')
    for task,(ca,cb) in DATA['counts'].items():
        if solution(a,b,F(cb,100),F(ca,100))[0]!=solution(b,a,F(ca,100),F(cb,100))[0]:raise ValueError('Swap regimes')
    summary=dict(source=DATA['source'],target_ids=DATA['targets'],gaps=DATA['gaps'],pilot_counts=DATA['counts'],
                 min_without_pilot=str(a*b/(a+b)),min_charged=str(1+best),
                 best_tasks=sorted(k for k,v in costs.items() if F(v[0])==best),
                 columns=['uncharged worst excess','easy prob after miss','easy prob after hit','excess regime A','excess regime B'],candidates=costs)
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('pilot.json',json.dumps(summary,sort_keys=True))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()

