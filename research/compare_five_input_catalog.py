"""Compare upper circuits to Blair Seidler's published MonoCatFileA5var.txt.

Source: https://sites.math.rutgers.edu/~bas312/Research/slp/MonoCatFileA5var.txt
Invoke with the path to that file. Only classes using all five variables are
compared. The tabulated assignments and both circuit descriptions are checked.
"""
from ast import literal_eval
from collections import Counter
import argparse
import re
from pathlib import Path
from five_input_catalog import verify_catalog,permutations_of,INPUTS

def compare(path):
    rows=verify_catalog()
    classes={g:r for r in rows for g in permutations_of(int(r['table'],16))}
    old=path.read_text().splitlines()
    results=[];seen=set()
    for i,line in enumerate(old):
        m=re.fullmatch(r'(\d+): \{(.*)\}',line)
        if not m:continue
        true_points=literal_eval('['+m[2]+']')
        f=sum(1<<sum((val==1)<<j for j,val in enumerate(x)) for x in true_points)
        if f not in classes:continue
        r=classes[f]
        plan=literal_eval(old[i+1])
        assert plan[:5]==[[j] for j in range(1,6)]
        wires=list(INPUTS)
        for op,a,b in plan[5:]:
            assert 1<=a<=len(wires) and 1<=b<=len(wires) and op in (1,5)
            wires.append(wires[a-1]&wires[b-1] if op==1 else wires[a-1]|wires[b-1])
        assert wires[-1]==f and r['table'] not in seen
        seen.add(r['table'])
        results.append((int(m[1]),r['table'],len(plan)-5,len(r['plan'])))
    assert len(results)==180
    return results

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source',type=Path);a=p.parse_args()
    result=compare(a.source)
    print('old gate count minus verified upper',dict(sorted(Counter(old-new for _,_,old,new in result).items())))
    for number,table,old,new in result:
        if old!=new:print(number,table,old,new)
