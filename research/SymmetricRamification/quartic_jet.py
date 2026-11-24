"""Order-four equations above the one surviving F3 orbit in ramification index 3."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json
import numpy as np
from sympy import GF
from sympy.polys.rings import ring
from hensel_planes import rref,terms,equations
from ramified_three import kernel

w=Path(__file__).resolve().parent
names=['w',*['t'+str(i) for i in range(6)],'u']
R,z,*other=ring(' '.join(names),GF(3))
ts=other[:6]
unit=other[-1]
def dot(c,v):
    return sum((int(k)*x for k,x in zip(c,v) if int(k)%3),R.zero)
def coords(U):
    a=[]
    for row in U:
        a.extend([*row,-2*sum(row[:6])-sum(row[6:])])
    return a
blocks=[Counter(tuple(sorted(map(int,t))) for t in ar) for ar in terms.values()]

def jet(B,orders,n):
    vectors=[coords(B),*[coords(v) for v in orders]]
    fields=[[R(int(e)%3) for e in vectors[0]]]+list(vectors[1:])
    @lru_cache(None)
    def series(key):
        if not key:return (R.one,*[R.zero]*n)
        acc=series(key[:-1])
        j=key[-1]
        return tuple(sum((fields[k][j]*acc[r-k] for k in range(min(r,len(fields)-1)+1)
                          if fields[k][j] and acc[r-k]),R.zero) for r in range(n+1))
    return [sum((int(c%3)*series(key)[n] for key,c in blk.items() if c%3),R.zero) for blk in blocks]

def generate():
    B=np.array(json.loads((w/'symmetric-hensel-three.json').read_bytes())[5]['basis'],dtype=np.int64)
    _,pivot=rref(B)
    free=[(i,j) for i in range(3) for j in range(9) if j not in pivot]
    M=np.zeros((18,3,9),dtype=np.int64)
    for k,(i,j) in enumerate(free):M[k,i,j]=1
    F=equations(np.concatenate(([B],B+3*M)))
    A=((F[1:]-F[0])//3).T%3
    b=F[0]//3%3
    K=kernel(A)
    left=kernel(A.T)
    _,pc=rref(A)
    _,pr=rref(A.T)
    inv=rref(np.column_stack((A[pr,:][:,pc],np.eye(len(pc),dtype=np.int64))))[0][:,len(pc):]
    def fill(vec):
        data=[[R.zero for _ in range(9)] for _ in range(3)]
        for (i,j),v in zip(free,vec):data[i][j]=v
        return data
    def normal(q):
        out=[R.zero]*18
        for i,j in enumerate(pc): out[j]=-dot(inv[i],[q[k] for k in pr])
        return out
    def proj(q):
        return [dot(r,q) for r in left]
    D=fill([int(c)*z+int(d)*(1-z) for c,d in zip(K[3],K[5])])
    Q=jet(B,[D],2)
    assert not any(proj(Q))
    E=fill([v+dot(K[:,j],ts) for j,v in enumerate(normal(Q))])
    C=[v+int(k) for v,k in zip(jet(B,[D,E],3),b)]
    assert not any(proj(C))
    G=fill(normal(C))
    Q4=jet(B,[D,E,G],4)
    DD=(K@M.reshape(18,-1)).reshape(-1,3,9)
    def first(v):
        f,g,h,i=equations([B+v,B-v,B+2*v,B-2*v])
        n=8*(f-g)-(h-i)
        assert (n%36==0).all()
        return (n//36)%3
    a,h=first(DD[3]),first(DD[5])
    Q4=[v+int(c)*z+int(d)*(1-z)+int(e)*unit for v,c,d,e in zip(Q4,a,h,b)]
    # Kernel ambiguity of the third coefficient contributes P*H(D,K_i).
    def qnum(v):
        f,g,h,i=equations([B+v,B-v,B+2*v,B-2*v])
        return ((16*(f+g-2*F[0])-(h+i-2*F[0]))//24)%3
    for i in (3,5):
        for v in DD:
            assert not (left@(qnum(DD[i]+v)-qnum(DD[i])-qnum(v))%3).any()
    polys=[p for p in proj(Q4) if p]
    def formatp(poly):
        out=[]
        for ex,c in poly.items():
            factors=[s if k==1 else s+'^'+str(k) for s,k in zip(names,ex) if k]
            if int(c)!=1 or not factors: factors.insert(0,str(int(c)))
            out.append('*'.join(factors))
        return '+'.join(out)
    dest=w/'ramified-quartic'/'3'
    dest.mkdir(exist_ok=True,parents=True)
    (dest/'05.in').write_text(','.join(names)+'\n3\n'+',\n'.join(map(formatp,polys))+'\n',newline='\n')
    print('order four',len(polys),'equations',flush=True)

if __name__=='__main__':
    generate()
