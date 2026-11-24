"""Integral truncated series in a uniformizer with pi^3=3."""
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import numpy as np
from sympy import ZZ
from sympy.polys.rings import ring
from hensel_planes import rref,terms,equations
from ramified_three import kernel

w=Path(__file__).resolve().parent
names=['w','t0','t1','t3','t5',*['r'+str(i) for i in range(6)],*['h'+str(i) for i in range(6)],'unit2']
R,*vars=ring(' '.join(names),ZZ)
vv=dict(zip(names,vars))
blocks=[Counter(tuple(sorted(map(int,ar))) for ar in data) for data in terms.values()]
def reducep(x,n=3):
    return R.from_dict({m:int(c)%n for m,c in x.items() if int(c)%n})
def quotient(x,n):
    assert all(int(c)%n==0 for c in x.values())
    return R.from_dict({m:int(c)//n for m,c in x.items()})
def dot(row,polys):
    return reducep(sum((int(v)*e for v,e in zip(row,polys) if int(v)%3),R.zero))
def state(B,orders,degree):
    def flat(A):
        return [a for row in A for a in [*row,-2*sum(row[:6])-sum(row[6:])]]
    F=[list(map(lambda n:R(int(n)),flat(B))),*[flat(O) for O in orders]]
    # Only residues modulo 3^(floor(degree/3)+1) affect this digit.
    power=3**(1+degree//3)
    @lru_cache(None)
    def conv(key):
        if not key:return (R.one,*[R.zero]*degree)
        prev=conv(key[:-1])
        j=key[-1]
        return tuple(reducep(sum((F[s][j]*prev[n-s] for s in range(min(n,len(F)-1)+1)
                                  if F[s][j] and prev[n-s]),R.zero),power) for n in range(degree+1))
    ans=[]
    for block in blocks:
        p=R.zero
        for k in range(degree%3,degree+1,3):
            p+=3**(k//3)*sum((c*conv(key)[k] for key,c in block.items()),R.zero)
        ans.append(reducep(quotient(p,3**(degree//3))))
    return ans

def build():
    plane=json.loads((w/'symmetric-hensel-three.json').read_bytes())[5]
    B=np.array(plane['basis'],dtype=np.int64)
    free=[(i,j) for i in range(3) for j in range(9) if j not in plane['pivots']]
    basis=np.zeros((18,3,9),dtype=np.int64)
    for k,(i,j) in enumerate(free):basis[k,i,j]=1
    E=equations(np.concatenate(([B],B+3*basis)))
    A=((E[1:]-E[0])//3).T%3
    b=E[0]//3%3
    K=kernel(A); left=kernel(A.T)
    _,pc=rref(A); _,pr=rref(A.T)
    inv=rref(np.column_stack((A[pr,:][:,pc],np.eye(len(pc),dtype=np.int64))))[0][:,len(pc):]
    def fill(v):
        a=[[R.zero]*9 for _ in range(3)]
        for (i,j),x in zip(free,v):a[i][j]=reducep(x)
        return a
    def kernel_part(v):
        return [dot(row,v) for row in K.T]
    def reduce_normal(q,tan):
        v=kernel_part(tan)
        for i,j in enumerate(pc):v[j]-=dot(inv[i],[q[k] for k in pr])
        return fill(v)
    z=vv['w']
    orders=[fill(kernel_part([R.zero,R.zero,R.zero,z,R.zero,1-z]))]
    for k,tag in [(2,'t'),(3,'r'),(4,'h')]:
        q=state(B,orders,k)
        check=[dot(r,q) for r in left]
        assert not any(check),(k,check)
        orders.append(reduce_normal(q,[vv.get(tag+str(i),R.zero) for i in range(6)]))
    fifth=state(B,orders,5)
    # For 3/pi^3 = 1+unit2*pi^2+..., the extra order-five term is unit2*(F(B)/3).
    projected=[dot(r,[x+int(c)*vv['unit2'] for x,c in zip(fifth,b)]) for r in left]
    polynomials=list(dict.fromkeys(str(p).replace('**','^').replace(' ','') for p in projected if p))
    dest=w/'ramified-quintic'/'3'
    dest.mkdir(exist_ok=True,parents=True)
    (dest/'05.in').write_text(','.join(names)+'\n3\n'+',\n'.join(polynomials)+'\n',newline='\n')
    print(len(polynomials),'fifth-order obstruction equations',flush=True)
if __name__=='__main__':build()
