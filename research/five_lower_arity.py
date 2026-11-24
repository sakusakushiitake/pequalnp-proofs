"""Extend the essential-variable calculation to every monotone five-input function.

For a nonconstant f with d unused coordinates, multiply f by those d variables
using AND. The product g is essential. A circuit for f of size s gives a circuit
for g of size s+d. Conversely we explicitly specialize a minimum monotone
circuit for g, then check all 32 outputs and that its size is exactly opt(g)-d.
"""
from collections import Counter
from itertools import permutations
from functools import reduce
import argparse,json,operator
from pathlib import Path
from five_input_catalog import INPUTS,monotone_tables,permutations_of,verify_catalog

FULL=(1<<32)-1
def evaluate(plan,output):
    wires=list(INPUTS)
    for gate in plan:
        op,*args=gate
        if op=='and':wires.append(reduce(operator.and_,(wires[j] for j in args),FULL))
        else:
            assert op=='or'
            wires.append(reduce(operator.or_,(wires[j] for j in args),0))
    return wires[output] if output<len(wires) else 0

def relabel(plan,target):
    for perm in permutations(range(5)):
        result=[[op,perm[a] if a<5 else a,perm[b] if b<5 else b] for op,a,b in plan]
        if evaluate(result,4+len(result))==target:return result
    raise ValueError('table outside orbit')

def specialize(plan,unused):
    remap=[None if j in unused else j for j in range(5)]
    new=[];seen={}
    for op,a,b in plan:
        a,b=remap[a],remap[b]
        if a is None or b is None:
            v=None if op=='or' else b if a is None else a
        elif a==b:v=a
        else:
            key=op,min(a,b),max(a,b)
            if key not in seen:seen[key]=5+len(new);new.append(list(key))
            v=seen[key]
        remap.append(v)
    selected=remap[-1];assert selected is not None
    live={selected}
    for k in reversed(range(len(new))):
        if 5+k in live:live.update(new[k][1:])
    ren={i:i for i in range(5)};result=[]
    for k,(op,a,b) in enumerate(new):
        if 5+k in live:ren[5+k]=5+len(result);result.append([op,ren[a],ren[b]])
    return result,ren[selected]

def all_classes():
    essential=verify_catalog()
    representatives={x:r for r in essential for x in permutations_of(int(r['table'],16))}
    remaining=monotone_tables(5)-representatives.keys()
    extra=[]
    while remaining:
        f=min(remaining);orbit=set(permutations_of(f));remaining.difference_update(orbit)
        unused=[i for i in range(5) if all(((f>>x)^(f>>(x^(1<<i))))&1==0 for x in range(32))]
        if f in (0,FULL):
            plan=[] if f==0 else [['and']]
            r=dict(table=f'{f:08x}',orbit=1,unused=unused,plan=plan,output=5)
        else:
            g=f & reduce(operator.and_,(INPUTS[i] for i in unused),FULL)
            reference=representatives[g];aligned=relabel(reference['plan'],g)
            plan,out=specialize(aligned,unused)
            assert len(plan)==len(aligned)-len(unused)
            r=dict(table=f'{f:08x}',orbit=len(orbit),unused=unused,plan=plan,output=out,
                   padded_table=f'{g:08x}',padded_class=reference['table'])
        assert evaluate(r['plan'],r['output'])==f
        extra.append(r)
    assert len(extra)==30 and sum(r['orbit'] for r in extra)==687
    return essential,extra

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--write',type=Path);args=p.parse_args()
    essential,extra=all_classes()
    hist=Counter();classes=Counter()
    for r in essential+extra:
        k=len(r['plan']);hist[k]+=r['orbit'];classes[k]+=1
    print('all',sum(hist.values()),'rows',dict(sorted(hist.items())))
    print('classes',sum(classes.values()),dict(sorted(classes.items())))
    if args.write:args.write.write_text(json.dumps(extra,indent=1)+'\n')
