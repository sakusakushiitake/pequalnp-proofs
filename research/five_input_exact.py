"""Exact synthesis below the upper bounds in five_input_catalog.py (python-sat).

Search each candidate size separately. --first selects one possible first
gate, numbered from zero in sorted order; omitting it covers all of them.
--dimacs emits the same formula for independent SAT solving or LRAT checking.
The truth constraints always use all 32 input assignments.
"""
import argparse
from functools import lru_cache
from itertools import combinations,permutations
from pathlib import Path
from five_input_catalog import INPUTS,verify_catalog
from five_input_shard import CNF,IDPool,CardEnc
from pysat.solvers import Solver

@lru_cache(None)
def symmetries(f):
    return [p for p in permutations(range(5)) if all(
        (f>>x)&1 == (f>>sum(((x>>i)&1)<<p[i] for i in range(5)))&1 for x in range(32))]

def canonical(f,k,first=None,not_limit=1,not_minimum=0):
    cnf,ids=CNF(),IDPool()
    gates=[];uses=[[] for _ in range(5+k)];nots=[]
    for w in range(5,5+k):
        choices={}
        # A minimal circuit has no constant, duplicate input, or unused gate.
        # Any essential input occurs. On its first gate a variable permutation
        # preserving the function may order the operands into the least orbit.
        for a,b in combinations(range(w),2):
            if w==5 and any(tuple(sorted((p[a],p[b]),reverse=True))<(b,a) for p in symmetries(f)):
                continue
            for op in ('and','or'):
                choices[b,a,op]=ids.id((w,b,a,op))
        for a in range(w):
            if w==5 and any(p[a]<a for p in symmetries(f)):
                continue
            s=ids.id((w,a,a,'not'));choices[a,a,'not']=s;nots.append(s)
        cnf.extend(CardEnc.equals(list(choices.values()),1,vpool=ids).clauses)
        for (b,a,op),s in choices.items():
            uses[a].append(s)
            if b!=a:uses[b].append(s)
            if gates:
                # A gate depending on its immediate predecessor necessarily
                # has a larger maximum operand. Independent adjacent gates
                # can be interchanged to obtain a lexicographically least order.
                for prev,old in gates[-1].items():
                    if prev>=(b,a,op):cnf.append([-old,-s])
            if b>=5 and op!='not':
                # Combining a binary gate with one of its own inputs simplifies
                # to that gate or that input, by absorption and idempotence.
                for (v,u,kind),old in gates[b-5].items():
                    if kind!='not' and a in (v,u):cnf.append([-s,-old])
        gates.append(choices)
    cnf.extend(uses[:-1])
    if not_limit is not None:cnf.extend(CardEnc.atmost(nots,not_limit,vpool=ids).clauses)
    if not_minimum:cnf.extend(CardEnc.atleast(nots,not_minimum,vpool=ids).clauses)
    if first is not None:cnf.append([sorted(gates[0].items())[first][1]])
    for x in range(32):
        v=[ids.id(('value',w,x)) for w in range(5+k)]
        for j in range(5):cnf.append([v[j] if (x>>j)&1 else -v[j]])
        cnf.append([v[-1] if (f>>x)&1 else -v[-1]])
        for w,choices in enumerate(gates,5):
            for (b,a,op),s in choices.items():
                y,z,o=v[a],v[b],v[w]
                if op=='and':rules=[[-o,y],[-o,z],[o,-y,-z]]
                elif op=='or':rules=[[o,-y],[o,-z],[-o,y,z]]
                else:rules=[[o,y],[-o,-y]]
                cnf.extend([[-s,*c] for c in rules])
    return cnf,gates

def check(f,k,first,not_limit=1):
    cnf,gates=canonical(f,k,first,not_limit)
    with Solver(name='cadical195',bootstrap_with=cnf.clauses) as solver:
        if not solver.solve():return False
        model=set(solver.get_model());wires=list(INPUTS);plan=[]
        for choices in gates:
            b,a,op=next(g for g,s in choices.items() if s in model)
            val=wires[a]&wires[b] if op=='and' else wires[a]|wires[b] if op=='or' else (~wires[a])&0xffffffff
            wires.append(val);plan.append((op,a,b))
        assert wires[-1]==f
        return plan

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('target',type=lambda s:int(s,16));p.add_argument('--size',type=int)
    p.add_argument('--first',type=int);p.add_argument('--dimacs',type=Path)
    p.add_argument('--unrestricted',action='store_true',help='allow any number of NOT gates')
    a=p.parse_args();rows=verify_catalog()
    limit=None if a.unrestricted else 1
    row=next(r for r in rows if int(r['table'],16)==a.target)
    if a.dimacs:
        if not a.size:p.error('--dimacs requires --size')
        cnf,gates=canonical(a.target,a.size,a.first,limit)
        cnf.to_file(str(a.dimacs))
        print('possible first gates',len(gates[0]),'variables',cnf.nv,'clauses',len(cnf.clauses))
    else:
        for k in ([a.size] if a.size else range(4,len(row['plan']))):
            result=check(a.target,k,a.first,limit)
            print(row['table'],k,'UNSAT' if result is False else result,flush=True)
