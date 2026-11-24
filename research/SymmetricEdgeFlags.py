"""Necessary edge-projection ranks for a complex symmetric permanent three-plane.

Use python SymmetricEdgeFlags.py --msolve /path/to/msolve (SymPy and msolve).
Coordinates 0,...,8 are 01,02,03,12,13,23,00,11,22. The first-degree
coefficient of per(J+tX) fixes 33. A Schubert cell has increasing pivots q.
The rank of projection to the first j coordinates is #{a in q : a < j}.
The closed Schubert condition q >= b (coordinatewise) is therefore a
collection of upper bounds on ranks, valid after any field extension.

We verify emptiness over the algebraic closure of F_32003 for three closed
unions of cells. This excludes each union over C. A complex point of a
rational closed condition gives a number-field point by the Nullstellensatz.
At a place above 32003 choose a full-rank basis minor of least valuation
and normalize it to the identity. Cramer's rule puts the basis entries in
the valuation ring. Reduction preserves overall rank, the permanent identity,
and every upper bound on ranks. It can change the individual Schubert cell.

Consequences for any prospective 3-space: every off-diagonal functional
is nonzero, the six off-diagonal functionals span the full dual, and whenever
01 and 02 are dependent the four 01,02,03,12 together span the full dual.
All statements persist under simultaneous permutations of the four labels.
"""
from collections import defaultdict
from itertools import combinations,permutations
from pathlib import Path
from math import gcd
from functools import reduce
from sympy import ZZ
from sympy.polys.rings import ring

ij=list(combinations(range(4),2))+[(i,i) for i in range(4)]
idx={x:i for i,x in enumerate(ij)}
terms=[[idx[tuple(sorted((i,j)))] for i,j in enumerate(p)] for p in permutations(range(4))]

def generate(piv,prime):
    free=[(i,j) for i,q in enumerate(piv) for j in range(q+1,9) if j not in piv]
    names=['x'+str(i) for i in range(max(1,len(free)))]
    R,a,b,c,*x=ring(' '.join(['a','b','c']+names),ZZ)
    U,*unused=ring(' '.join(names),ZZ)
    m=[[R.zero for _ in range(9)] for _ in range(3)]
    for i,j in enumerate(piv):
        m[i][j]=R.one
    for k,(i,j) in enumerate(free):
        m[i][j]=x[k]
    for row in m:
        row.append(-2*sum(row[:6])-sum(row[6:]))
    vals=[1+a*m[0][j]+b*m[1][j]+c*m[2][j] for j in range(10)]
    f=sum(vals[i]*vals[j]*vals[k]*vals[l] for i,j,k,l in terms)-24
    groups=defaultdict(dict)
    for mon,coef in f.items():
        assert 2<=sum(mon[:3])<=4
        groups[mon[:3]][mon[3:]]=coef
    polys=[]
    for ex,coeffs in sorted(groups.items()):
        if prime:
            coeffs={m:int(c)%prime for m,c in coeffs.items() if int(c)%prime}
            if not coeffs:
                continue
        div=reduce(gcd,(abs(int(v)) for v in coeffs.values()))
        assert not prime or gcd(div,prime)==1
        g=U.from_dict({k:v//div for k,v in coeffs.items()})
        if g.is_ground:
            return names,['1']
        polys.append(str(g).replace('**','^').replace(' ',''))
    return names,polys or ['0']


def verify(binary):
    import subprocess
    from tempfile import TemporaryDirectory
    from sympy import isprime
    prime=32003
    assert isprime(prime)
    bounds=[(1,2,3),(0,2,4),(0,1,6)]
    cells=list(combinations(range(9),3))
    selected=[q for q in cells if any(all(i>=j for i,j in zip(q,b)) for b in bounds)]
    assert len(selected)==79
    with TemporaryDirectory() as tmp:
        folder=Path(tmp)
        for q in selected:
            names,eq=generate(q,prime)
            source=folder/(''.join(map(str,q))+'.in')
            out=source.with_suffix('.out')
            source.write_text(','.join(names)+'\n'+str(prime)+'\n'+',\n'.join(eq)+'\n',encoding='ascii')
            proc=subprocess.run([binary,'-f',str(source),'-o',str(out),'-t','2','-l','2'],capture_output=True)
            assert proc.returncode==0 and out.read_text().strip()=='[-1]:',q
            print(q,'empty',flush=True)
    print('All 79 cells in the three closed Schubert conditions are empty.')

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--msolve',default='msolve')
    verify(ap.parse_args().msolve)
