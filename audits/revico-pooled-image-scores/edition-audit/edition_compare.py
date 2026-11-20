"""Compare source-labelled scores for printed base models on pages 5 and 7."""
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
import json,re
def rows(page,expected,limit):
    txt=Path(page+'.txt').read_text()
    if page=='new5':txt=txt.split('Image + Vision Language Models')[1]
    if page in ('new5','new7'):txt=txt.split('Table ')[0]
    if page=='old7':txt=txt.split('Figure 6.')[0]
    result={}
    for line in txt.splitlines():
        cells=line.strip().replace('−','-').replace('±','+').split()
        if len(cells)!=expected+1:continue
        name=cells[0].replace('QwenVL','Qwen2.5VL').replace('–','-')
        if not name.startswith(('Qwen','Intern','GPT','Claude','Seed','Gemini')):continue
        scores=[re.fullmatch(r'(\d+\.\d+)([+-]\d+\.\d+)?',k) for k in cells[1:]]
        if not all(scores):continue
        if name in result:raise ValueError(name)
        result[name]=[(m[1],m[2]) for m in scores]
    if len(result)!=limit:raise ValueError((page,len(result),list(result)))
    return result
a=rows('old5',12,11);b=rows('old7',12,10);c=rows('new5',12,20);d=rows('new7',8,20)
labels=['ID','TD','IC','TC'];order=[0,2,1,3]
def measures(arr,indices):
    return [F(arr[i][0]) for i in indices]
common=sorted(a.keys()&b.keys()&c.keys()&d.keys())
if len(common)!=9:raise ValueError(common)
names=['0123','0213'];results={};totals=[0]*4
for model in common:
    orig=measures(a[model],(2,5,8,11))
    olddirect=measures(b[model],[3*j for j in order])
    oldbg=measures(b[model],[3*j+2 for j in order])
    latest=measures(d[model],(0,2,4,6))
    bg=measures(d[model],(1,3,5,7))
    perm=[''.join(map(str,p)) for p in permutations(range(4)) if [orig[j] for j in p]==olddirect]
    results[model]=dict(old_direct_permutations=perm,new_direct_unequal=[labels[j] for j in range(4) if latest[j]!=orig[j]],background_mismatches=[labels[j] for j in range(4) if oldbg[j]!=bg[j]],old_to_new_direct_differences=[labels[j] for j in range(4) if olddirect[j]!=latest[j]])
    for j in range(4):totals[j]+=oldbg[j]==bg[j]
inter=sorted(a.keys()&c.keys())
diff=[(k,i,a[k][i][0],c[k][i][0]) for k in inter for i in range(12) if F(a[k][i][0])!=F(c[k][i][0])]
def signed(x):return (x>0)-(x<0)
signs=[]
for k in common:
    for j,i in enumerate(order):
        olddirect,oldbg=measures(b[k],(3*i,3*i+2));newdirect,newbg=measures(d[k],(2*j,2*j+1))
        if signed(oldbg-olddirect)!=signed(newbg-newdirect):
            signs.append(dict(model=k,metric=labels[j],old=[str(olddirect),str(oldbg)],new=[str(newdirect),str(newbg)]))
def delta_errors(table,step,metric_labels):
    bad=[]
    for k,row in table.items():
        for j in range(4):
            start=F(row[step*j][0])
            for offset in range(1,step):
                end,printed=row[step*j+offset]
                calc=F(end)-start
                if abs(calc-F(printed))>F(15,100):
                    bad.append(dict(model=k,metric=metric_labels[j],prompt=('background' if offset==step-1 else 'ocr'),start=str(start),end=end,printed=printed,computed=str(calc)))
    return bad
print(json.dumps(dict(shared=common,all_main_table_rows=inter,main_table_differences=diff,comparisons=results,background_identical_by_metric=totals,sign_changes=signs,older_delta_mismatches=delta_errors(b,3,['ID','IC','TD','TC']),later_delta_mismatches=delta_errors(d,2,labels))))