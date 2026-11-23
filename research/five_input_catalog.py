"""Validate the 180 essential monotone classes and their upper circuits.

Run without arguments next to the six five_catalog_*.json files. Set --cnf
with a hexadecimal --target to emit the unrestricted wiring CNF at upper-1.
Each optional certificate field is [excluded size, LRAT actions, proof bytes,
DIMACS SHA-256, binary LRAT SHA-256]. A recorded digest identifies a checked
artifact. Running this program alone checks the catalog and the upper bounds.
"""
import argparse
from collections import Counter
from itertools import permutations
import json
from pathlib import Path

DIRECTORY=Path(__file__).resolve().parent
INPUTS=tuple(sum(1<<x for x in range(32) if (x>>i)&1) for i in range(5))

def monotone_tables(n):
    if not n:
        return {0,1}
    smaller=monotone_tables(n-1)
    return {lo|(hi<<(1<<(n-1))) for lo in smaller for hi in smaller if lo & hi == lo}

def permutations_of(f):
    for p in permutations(range(5)):
        image=0
        for x in range(32):
            y=sum(((x>>i)&1)<<p[i] for i in range(5))
            image|=((f>>x)&1)<<y
        yield image

def verify_catalog(directory=DIRECTORY):
    rows=[r for file in sorted(directory.glob('five_catalog_??_??.json')) for r in json.loads(file.read_text())]
    assert sorted((r['shard'],r['index']) for r in rows)==[(s,i) for s in range(1,19) for i in range(10)]
    covered={}
    for r in rows:
        f=int(r['table'],16)
        wires=list(INPUTS)
        for op,a,b in r['plan']:
            assert 0<=a<=b<len(wires) and op in ('and','or')
            wires.append(wires[a]&wires[b] if op=='and' else wires[a]|wires[b])
        assert wires[-1]==f
        orbit=set(permutations_of(f))
        assert len(orbit)==r['orbit'] and covered.keys().isdisjoint(orbit)
        covered.update(dict.fromkeys(orbit,f))
    all_monotone=monotone_tables(5)
    essential={f for f in all_monotone if all(any(((f>>x)^(f>>(x^(1<<i))))&1 for x in range(32)) for i in range(5))}
    assert set(covered)==essential and len(all_monotone)==7581 and len(essential)==6894
    for r in rows:
        f=int(r['table'],16)
        dual=sum((1-((f>>(31-x))&1))<<x for x in range(32))
        assert covered[dual]==int(r['dual'],16)
    return rows

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--target',type=lambda s:int(s,16));p.add_argument('--cnf',type=Path)
    a=p.parse_args();rows=verify_catalog()
    print('7581 monotone tables, 6894 essential tables, 180 permutation classes')
    print('upper size -> classes',dict(sorted(Counter(len(r['plan']) for r in rows).items())))
    print('direct raw-CNF certificate records',sum('certificate' in r for r in rows))
    if a.cnf:
        if a.target is None:p.error('--cnf needs --target')
        from five_input_shard import instance
        r=next(r for r in rows if int(r['table'],16)==a.target)
        instance(a.target,len(r['plan'])-1).to_file(str(a.cnf))
