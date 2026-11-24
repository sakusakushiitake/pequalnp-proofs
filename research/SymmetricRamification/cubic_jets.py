"""Order-three lifting equations in ramification index three, one representative per S4 orbit."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import json
import numpy as np
from sympy import GF
from sympy.polys.rings import ring
from hensel_planes import rref,equations
from ramified_three import kernel
from three_orbits import orbits

w=Path(__file__).resolve().parent
def compute(ix,entry):
    B=np.array(entry['basis'],dtype=np.int64)
    Piv=entry['pivots']
    free=[(i,j) for i in range(3) for j in range(9) if j not in Piv]
    M=np.zeros((18,3,9),dtype=np.int64)
    for k,(i,j) in enumerate(free):M[k,i,j]=1
    F=equations(np.concatenate(([B],B+3*M)))
    A=((F[1:]-F[0])//3).T%3
    b=F[0]//3%3
    K=kernel(A)
    left=kernel(A.T)
    _,cols=rref(A)
    _,rows=rref(A.T)
    rank=len(cols)
    P=A[rows,:][:,cols]
    inv=rref(np.column_stack((P,np.eye(rank,dtype=np.int64))))[0][:,rank:]
    assert np.array_equal(inv@P%3,np.eye(rank))
    D=(K@M.reshape(18,-1)).reshape(-1,3,9)
    d=len(D)
    names=['s'+str(i) for i in range(d)]+['t'+str(i) for i in range(d)]
    R,*ts=ring(' '.join(names),GF(3))
    s,t=ts[:d],ts[d:]
    def both(v):
        f,g,h,i=equations([B+v,B-v,B+2*v,B-2*v])
        q=16*(f+g-2*F[0])-(h+i-2*F[0])
        c=(h-i)-2*(f-g)
        assert (q%24==0).all() and (c%12==0).all()
        return (q//24)%3,(c//12)%3
    def polys(pairs):
        pairs=list(pairs)
        return [sum((int(v[j])*m for v,m in pairs if v[j]%3),R.zero) for j in range(len(pairs[0][0]))]
    def dot(a,polys):
        return sum((int(v)*m for v,m in zip(a,polys) if v%3),R.zero)
    qc=[both(e) for e in D]
    quadr=[(q,s[i]**2) for i,(q,_) in enumerate(qc)]
    cubic=[(left@c%3,s[i]**3) for i,(_,c) in enumerate(qc)]
    cpairs={}
    for i,j in combinations(range(d),2):
        qp,cp=both(D[i]+D[j])
        cm=both(D[i]-D[j])[1]
        cpairs[i,j]=cp
        quadr.append(((qp-qc[i][0]-qc[j][0])%3,s[i]*s[j]))
        cubic.extend([(left@((cp-cm)*2-qc[j][1])%3,s[i]**2*s[j]),
                      (left@((cp+cm)*2-qc[i][1])%3,s[i]*s[j]**2)])
    for i,j,k in combinations(range(d),3):
        c=both(D[i]+D[j]+D[k])[1]-cpairs[i,j]-cpairs[i,k]-cpairs[j,k]+qc[i][1]+qc[j][1]+qc[k][1]
        cubic.append((left@c%3,s[i]*s[j]*s[k]))
    Q=polys(quadr)
    final=[dot(row,Q) for row in left]
    cubic.append((left@b%3,R.one))
    C=polys(cubic)
    y=[dot(K[:,j],t) for j in range(18)]
    for i,j in enumerate(cols):
        y[j]-=dot(inv[i], [Q[r] for r in rows])
    qm=[both(v)[0] for v in M]
    for i in range(d):
        for j in range(18):
            if not y[j]: continue
            coeff=left@(both(D[i]+M[j])[0]-qc[i][0]-qm[j])%3
            mult=s[i]*y[j]
            for r,v in enumerate(coeff):
                if v: C[r]+=int(v)*mult
    def fmt(poly):
        terms=[]
        for ex,c in poly.items():
            factors=[s0 if k==1 else s0+'^'+str(k) for s0,k in zip(names,ex) if k]
            if int(c)!=1 or not factors: factors.insert(0,str(int(c)))
            terms.append('*'.join(factors))
        return '+'.join(terms)
    eqs=[fmt(e) for e in [*final,*C] if e]
    dest=w/'ramified-cubic'/'3'
    dest.mkdir(parents=True,exist_ok=True)
    (dest/(f'{ix:02d}.in')).write_text(','.join(names)+'\n3\n'+',\n'.join(eqs)+'\n',newline='\n')
    print(ix,d,len(eqs),flush=True)
if __name__=='__main__':
    families=json.loads((w/'symmetric-hensel-three.json').read_bytes())
    for orbit in orbits():
        compute(orbit[0],families[orbit[0]])
