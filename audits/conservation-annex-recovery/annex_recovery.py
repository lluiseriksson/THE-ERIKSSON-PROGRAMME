"""Compare archived name/annex relations. Exact text matches only."""
from collections import Counter, defaultdict
from pathlib import Path
import csv, io, hashlib, json, zipfile

def tables(path):
    result = {}
    with zipfile.ZipFile(path) as z:
        for member in z.namelist():
            f = Path(member)
            if f.stem.lower() not in ('nameusage','taxonproperty') or '__MACOSX' in f.parts:
                continue
            stream = io.StringIO(z.read(member).decode('utf-8-sig'))
            header = stream.readline()
            sep = max(['\t',',',';'], key=header.count)
            stream.seek(0)
            rows = csv.DictReader(stream, delimiter=sep)
            result[f.stem.lower()] = [{k.lower():v for k,v in r.items()} for r in rows]
    return result

def read_main(v):
    data=tables('archive-%d.zip'%v)
    names={r['id']:r['scientificname'] for r in data['nameusage']}
    relations={(names[r['taxonid']],r['property'],r['value']) for r in data['taxonproperty']}
    return set(names.values()), relations

def counts(proposed,reference):
    return dict(proposed=len(proposed),matched=len(reference & proposed),
                missing=len(reference-proposed),extra=len(proposed-reference),
                extra_examples=sorted(proposed-reference)[:8],missing_examples=sorted(reference-proposed)[:8])

def main():
    labels={'314945':'I','314974':'II','314380':'III','314298':'II','314304':'IV','314308':'V'}
    universe,old=read_main(12)
    newnames,new=read_main(13)
    if universe!=newnames or new-old:raise ValueError('Unexpected archive history')
    lost=old-new
    report={}
    certificates=[]
    for pin in json.loads(Path('companion-pins.json').read_text(encoding='utf-8-sig')):
        path=Path(pin['archive'])
        if hashlib.sha256(path.read_bytes()).hexdigest()!=pin['sha256']:raise ValueError(path)
        d=tables(path); ds=pin['dataset']; rows=d['nameusage']; props=d.get('taxonproperty',[])
        names={r['id']:r for r in rows}
        allnames={r['scientificname'] for r in rows}
        if len(names)!=len(rows) or any(r['taxonid'] not in names for r in props):raise ValueError(ds)
        if ds not in labels:
            report[ds]=dict(role='habitat characterization, different relation',shared_names=len(allnames&universe),property_types=sorted({r['property'] for r in props}));continue
        birds=ds in ('314945','314974','314380')
        prop='EU '+('Birds' if birds else 'Habitats')+' Directive annex'
        level=labels[ds]
        def subset(base):
            return {(n,v) for n,p,v in base if p==prop and v.split('/')[0]==level}
        target=subset(lost); full=subset(old)
        reference={n for n,v in target}
        available=allnames & universe
        roles={n for n in available if any(r['scientificname']==n and r.get('rank','') in ('species','subspecies','variety','form') for r in rows)}
        detail=dict(title=pin['title'],annex=level,within_universe=len(available),all_rows=len(rows),all_names=len(allnames),
                    missing_exact_relations=len(target),presence_broad=counts(available,reference))
        if birds:
            mapping={'I':'I','II PART A':'II/A','II PART B':'II/B','III PART A':'III/A','III PART B':'III/B'}
            values=Counter(r['value'] for r in props)
            evidence={(names[r['taxonid']]['scientificname'],mapping[r['value']]) for r in props if r['value'] in mapping and r['property']=='Birds Directive Annex'} 
            evidence={x for x in evidence if x[0] in universe}
            detail.update(property_values=dict(values),unmapped_values=sorted(values.keys()-mapping.keys()),explicit_exact=counts(evidence,target),
                          explicit_broad=counts({n for n,v in evidence},reference))
        else:
            evidence={(n,level) for n in available}
            detail.update(rank_filtered=counts(roles,reference),
                          outside_reference_ranks=dict(Counter(r['rank'] for r in rows if r['scientificname'] in available-reference)))
        detail['comparison_all_v12']=counts(evidence,full)
        certificates.extend([dict(dataset=ds,name=n,value=v,evidence='explicit property' if birds else 'name in annex file',
                                  lost=(n,v) in target,old=(n,v) in full) for n,v in sorted(evidence)])
        report[ds]=detail
    out=dict(unique_lost=len(lost),by_dataset=report,certificates=certificates)
    Path('reconstruction.json').write_text(json.dumps(out,sort_keys=True,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
