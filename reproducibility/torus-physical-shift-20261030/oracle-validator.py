import json, re, sys, pathlib
NAMES=['finBoxZModEquiv_apply','finBoxZModEquiv_shift','finBoxZModEquiv_shiftBack','sunComplexPlane_sub','torusPhysicalEmbed_flat_div_apply','torusPhysicalEmbed_flat_curl_apply','torusPhysicalEmbed_flat_div_norm_sq']
PATTERN=r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def verify(content):
    matches=re.findall(PATTERN,content)
    if len(matches)!=7: raise ValueError('Wrong oracle count')
    checked=[]
    for (name,axs),want in zip(matches,NAMES):
        actual_ax=[x.strip() for x in axs.split(',') if x.strip()]
        if name!='YangMills.RG.'+want: raise ValueError('Wrong oracle name')
        if not set(actual_ax).issubset({'propext','Classical.choice','Quot.sound'}): raise ValueError('Unapproved axiom')
        if len(actual_ax)!=len(set(actual_ax)): raise ValueError('Repeated axiom')
        checked.append({'name':name,'axioms':actual_ax})
    return checked
if __name__=='__main__':
    raw=pathlib.Path(sys.argv[1]).read_text()
    verify(raw)
    hits=list(re.finditer(PATTERN,raw))
    mutations=[raw.replace(hits[0].group(1),hits[-1].group(1),1),
               raw[:hits[-1].start()]+raw[hits[-1].end():],
               raw.replace('propext','sorryAx',1)]
    rejected=0
    for bad in mutations:
        if bad==raw: raise RuntimeError('Mutation did not change real evidence')
        try: verify(bad)
        except ValueError: rejected+=1
        else: raise RuntimeError('Mutated evidence accepted')
    if rejected!=3: raise RuntimeError('Wrong rejection count')
    print(json.dumps({'status':'ORACLE_VALIDATOR_SELFTEST_PASS','real_mutations_rejected':rejected,'positive_accepted':1,'optimized':not __debug__}))
