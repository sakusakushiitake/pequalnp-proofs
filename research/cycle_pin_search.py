"""Search for a cycle circuit lacking every posted tight substitution.

Use --full to include constants, copies, arbitrary output gates and unused
gates. The cycle edge function is neither constant nor an input. With
--full, every fan-in-two AND/OR/NOT list is represented: empty or invalid
reads give constants, a one-input AND/OR is a copy, and a two-input NOT
reads only its first operand. Commutative operands can be sorted.

For a fixed pin, the number of gates that collapse is the gate count minus
the count of distinct restricted gate functions outside the constants and
input projections. A model must exhibit sufficiently many pairwise distinct
nontrivial functions for each pin. A SAT model is checked on all inputs.
Use --dimacs to generate an instance for a separate proof-producing solver.
"""
from itertools import combinations, product
from pathlib import Path
import argparse
import json
import sys
from time import monotonic

for deps in (Path(__file__).resolve().parent/'python',Path(__file__).resolve().parent.parent/'.pnp'/'python'):
    if deps.is_dir():sys.path.insert(0,str(deps))
from pysat.card import CardEnc
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def inputs(n):
    return [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]


def check(n, gates, output=None):
    full = (1 << (1 << n)) - 1
    vals = inputs(n)
    for op,a,b in gates:
        if op=='and': value=vals[a] & vals[b]
        elif op=='or': value=vals[a] | vals[b]
        elif op=='not': value=full ^ vals[a]
        elif op=='copy': value=vals[a]
        elif op=='true': value=full
        elif op=='false': value=0
        else: raise ValueError(op)
        vals.append(value)
    goal = sum(1 << x for x in range(1 << n) if any(x >> i & x >> ((i+1)%n) & 1 for i in range(n)))
    assert vals[-1 if output is None else output] == goal
    counts = []
    for p,b in product(range(n),range(2)):
        rows = vals[p] if b else full ^ vals[p]
        base = {0,rows} | {v & rows for v in vals[:n]}
        new = {v & rows for v in vals[n:]} - base
        counts.append(len(vals[n:])-len(new))
    return counts


def standard(n):
    edges = [(i,(i+1)%n) for i in range(n)]
    for picks in product(range(2),repeat=n):
        centers = {}
        for e,i in zip(edges,picks):
            centers.setdefault(e[i],[]).append(e[1-i])
        if len(centers)!=(n+1)//2:
            continue
        gates, terms = [], []
        for center, others in centers.items():
            neighbor = others[0]
            if len(others)>1:
                gates.append(('or',*others)); neighbor=n+len(gates)-1
            gates.append(('and',center,neighbor))
            terms.append(n+len(gates)-1)
        def trees(rest,ops):
            if len(rest)==1:
                yield ops
            else:
                for i,j in combinations(range(len(rest)),2):
                    gate=('or',rest[i],rest[j])
                    remaining=[v for k,v in enumerate(rest) if k not in (i,j)]
                    yield from trees(remaining+[n+len(ops)],ops+[gate])
        yield from trees(terms,gates)


def no_tight(n,k,conflicts,full=False,dimacs=None):
    ids, clauses=IDPool(),CNF()
    rows = range(1<<n)
    groups=[]
    def val(w,x): return ids.id(('v',w,x))
    out=[ids.id(('out',w)) for w in range(n,n+k)]
    if full: clauses.append(out)
    for x in rows:
        for w in range(n): clauses.append([val(w,x) if x>>w&1 else -val(w,x)])
        want=any(x>>i & x>>((i+1)%n) & 1 for i in range(n))
        if full:
            for w,s in enumerate(out,n):
                clauses.append([-s,val(w,x) if want else -val(w,x)])
        else: clauses.append([val(n+k-1,x) if want else -val(n+k-1,x)])
    users=[[] for _ in range(n+k)]
    for w in range(n,n+k):
        options = {}
        for a,b in combinations(range(w),2):
            if not full and w==n and (a or b>n//2): continue
            for op in ('and','or'): options[op,a,b]=ids.id(('g',w,op,a,b))
        for a in range(w):
            if not full and w==n and a: continue
            options['not',a,a]=ids.id(('g',w,'not',a))
            if full: options['copy',a,a]=ids.id(('g',w,'copy',a))
        if full:
            for op in ('true','false'): options[op,0,0]=ids.id(('g',w,op))
        clauses.extend(CardEnc.equals(list(options.values()),1,vpool=ids).clauses)
        for (op,a,b),s in options.items():
            users[a].append(s)
            if a!=b: users[b].append(s)
            for x in rows:
                u,t,z=val(a,x),val(b,x),val(w,x)
                if op=='and': cs=[[-z,u],[-z,t],[z,-u,-t]]
                elif op=='or': cs=[[z,-u],[z,-t],[-z,u,t]]
                elif op=='not': cs=[[z,u],[-z,-u]]
                elif op=='copy': cs=[[-z,u],[z,-u]]
                else: cs=[[z]] if op=='true' else [[-z]]
                clauses.extend([[-s,*c] for c in cs])
        groups.append(options)
    if not full: clauses.extend(users[:-1])
    for p,b in product(range(n),range(2)):
        subset=[x for x in rows if (x>>p)&1==b]
        chosen=[ids.id(('new',p,b,j)) for j in range(k)]
        threshold=4 if b else 3
        clauses.extend(CardEnc.atleast(chosen,k-threshold+1,vpool=ids).clauses)
        for j,s in enumerate(chosen,n):
            for mask in [0,(1<<len(subset))-1]+[sum(((x>>v)&1)<<t for t,x in enumerate(subset)) for v in range(n) if v!=p]:
                clauses.append([-s,*[-val(j,x) if mask>>t&1 else val(j,x) for t,x in enumerate(subset)]])
        for i,j in combinations(range(k),2):
            differences=[]
            for x in subset:
                d=ids.id(('different',i,j,x))
                differences.append(d)
                z,t=val(n+i,x),val(n+j,x)
                clauses.extend([[-d,z,t],[-d,-z,-t]])
            clauses.append([-chosen[i],-chosen[j],*differences])
    print('CNF',n,k,ids.top,len(clauses.clauses),flush=True)
    if dimacs:
        clauses.to_file(str(dimacs))
    with Solver(name='cadical195',bootstrap_with=clauses.clauses) as solver:
        solver.conf_budget(conflicts)
        start=monotonic(); status=solver.solve_limited()
        print('solver',status,'seconds',round(monotonic()-start,2),flush=True)
        if status:
            model=set(solver.get_model())
            gates=[next(key for key,s in options.items() if s in model) for options in groups]
            output=next(w for w,s in enumerate(out,n) if s in model) if full else n+k-1
            counts=check(n,gates,output)
            assert all(c < (4 if i%2 else 3) for i,c in enumerate(counts))
            return gates, output


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('n',type=int,choices=(5,6,7))
    parser.add_argument('--conflicts',type=int,default=30000)
    parser.add_argument('--full',action='store_true')
    parser.add_argument('--dimacs',type=Path)
    args=parser.parse_args()
    n=args.n; k=n+(n+1)//2-1
    examples = list(standard(n))
    bad=[]
    for gates in examples:
        counts=check(n,gates)
        if all(c < (4 if i%2 else 3) for i,c in enumerate(counts)):
            bad.append(gates)
    print('standard',len(examples),'without tight pin',len(bad),flush=True)
    witness=(bad[0],n+k-1) if bad else no_tight(n,k,args.conflicts,args.full,args.dimacs)
    if witness:
        path=Path(__file__).with_name(f'cycle-{n}-non-tight.json')
        path.write_text(json.dumps(witness))
        print('verified witness',witness,check(n,*witness),flush=True)
