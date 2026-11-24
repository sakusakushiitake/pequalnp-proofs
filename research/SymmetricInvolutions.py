"""Exclude involution-invariant complex 3-spaces on the symmetric permanent level.

Usage: python SymmetricInvolutions.py --msolve /path/to/msolve
Requires SymPy and msolve (tested with 0.9.4). Each cell is computed over the
algebraic closure of F_32003. There are 84 charts for each involution type.

A complex solution to these rational equations would exist over a number
field by the weak Nullstellensatz. Reduce the two Grassmannian points (one
for each sign) at a place above 32003. Within each sign, pick a full-rank
minor of least valuation and normalize it to the identity: Cramer's rule
makes all entries integral there and reduction preserves rank. The integral
polynomial identities would then hold on one of the reduced cells.
"""
from itertools import combinations,product
from collections import defaultdict
from pathlib import Path
import sympy as sy
from sympy.polys.rings import ring
from itertools import permutations

ij=list(combinations(range(4),2))+[(i,i) for i in range(4)]
idx={pos:k for k,pos in enumerate(ij)}
terms=[[idx[tuple(sorted((i,j)))] for i,j in enumerate(p)] for p in permutations(range(4))]

def basis(permutation,sign):
    remaining=set(ij)
    result=[]
    while remaining:
        a=min(remaining)
        b=tuple(sorted((permutation[a[0]],permutation[a[1]])))
        remaining.difference_update((a,b))
        if a==b and sign==-1:
            continue
        m=sy.zeros(4)
        m[a]=m[a[::-1]]=1
        m[b]=m[b[::-1]]=sign
        result.append(m)
    return result


def emit(root,prime,npositive,kind):
    involution=(1,0,3,2) if kind=='doubleswap' else (1,0,2,3)
    B=basis(involution,1)
    row=[sum(m) for m in B]
    pivot=next(i for i,x in enumerate(row) if x!=0)
    even=[int(row[pivot])*M-int(row[k])*B[pivot] for k,M in enumerate(B) if k!=pivot]
    odd=basis(involution,-1)
    nnegative=3-npositive
    folder=root/f'{kind}-{npositive}'
    folder.mkdir(exist_ok=True,parents=True)
    for pe,po in product(combinations(range(len(even)),npositive),
                         combinations(range(len(odd)),nnegative)):
        shapes=[(pe,even),(po,odd)]
        free=[(sign,i,j) for sign,(piv,base) in enumerate(shapes)
              for i,q in enumerate(piv) for j in range(q+1,len(base)) if j not in piv]
        names=['x'+str(i) for i in range(max(1,len(free)))]
        R,a,b,c,*xx=ring(' '.join(['a','b','c']+names),sy.ZZ)
        U,*_=ring(' '.join(names),sy.ZZ)
        form=[R.one for _ in ij]
        scalars=iter([a,b,c])
        lookup=dict(zip(free,xx))
        for sign,(piv,base) in enumerate(shapes):
            for i,q in enumerate(piv):
                scalar=next(scalars)
                for j,M in enumerate(base):
                    amp=R.one if j==q else lookup.get((sign,i,j),R.zero)
                    if amp:
                        for k,p in enumerate(ij):
                            form[k]+=scalar*amp*int(M[p])
        f=sum(form[i]*form[j]*form[k]*form[l] for i,j,k,l in terms)-24
        groups=defaultdict(dict)
        for mon,coeff in f.items():
            assert sum(mon[:3])>=2
            v=int(coeff)%prime if prime else int(coeff)
            if v:
                groups[mon[:3]][mon[3:]]=v
        polys=[]
        for data in groups.values():
            p=U.from_dict(data)
            if p.is_ground:
                polys=['1'];break
            polys.append(str(p).replace('**','^').replace(' ',''))
        name=''.join(map(str,pe))+'_'+''.join(map(str,po))
        (folder/(name+'.in')).write_text(','.join(names)+'\n'+str(prime)+'\n'+',\n'.join(polys or ['0'])+'\n',encoding='ascii',newline='\n')


def verify(binary):
    import subprocess
    from tempfile import TemporaryDirectory
    from math import comb
    prime=32003
    assert sy.isprime(prime)
    with TemporaryDirectory() as tmp:
        root=Path(tmp)
        def solve(path):
            result=path.with_suffix('.out')
            subprocess.run([binary,'-f',str(path),'-o',str(result),'-t','1','-l','2'],
                           check=True,capture_output=True)
            output=result.read_text().strip()
            assert output
            return output
        control=root/'control.in'
        control.write_text(f'x\n{prime}\nx,x-1\n')
        assert solve(control)=='[-1]:'
        # x^2+1 has no F_p root (p = 3 mod 4) but has algebraic roots.
        control.write_text(f'x\n{prime}\nx^2+1\n')
        assert solve(control)!='[-1]:'
        for kind in ('singleswap','doubleswap'):
            checked=0
            for npositive in range(4):
                emit(root,prime,npositive,kind)
                directory=root/f'{kind}-{npositive}'
                for path in sorted(directory.glob('*.in')):
                    assert solve(path)=='[-1]:', (kind,npositive,path.stem)
                    checked+=1
            assert checked==comb(9,3)
            print(kind,checked,'empty cells')


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--msolve',default='msolve')
    verify(ap.parse_args().msolve)
