"""Second-order obstruction at the 32 rational special-fibre planes above 3."""
from pathlib import Path
from itertools import combinations
import json
import numpy as np
from hensel_planes import rref,equations

w=Path(__file__).resolve().parent

def kernel(A):
    E,pivs=rref(A)
    free=[j for j in range(E.shape[1]) if j not in pivs]
    D=np.zeros((len(free),E.shape[1]),dtype=np.int64)
    for i,j in enumerate(free):
        D[i,j]=1
        for k,p in enumerate(pivs): D[i,p]=-E[k,j]%3
    assert (A@D.T%3==0).all()
    return D

def generate():
    planes=json.loads((w/'symmetric-hensel-three.json').read_bytes())
    dest=w/'ramified-two'/'3'
    dest.mkdir(exist_ok=True,parents=True)
    for ix,entry in enumerate(planes):
        B=np.array(entry['basis'])
        free=[(i,j) for i in range(3) for j in range(9) if j not in entry['pivots']]
        moves=np.zeros((18,3,9),dtype=np.int64)
        for k,(i,j) in enumerate(free): moves[k,i,j]=1
        E=equations(np.concatenate(([B],B+3*moves)))
        A=((E[1:]-E[0])//3).T%3
        b=E[0]//3%3
        K=kernel(A)
        left=kernel(A.T)
        D=(K@moves.reshape(18,-1)).reshape(-1,3,9)
        def quadratic(V):
            f=equations([B+V,B-V,B+2*V,B-2*V])
            num=16*(f[0]+f[1]-2*E[0])-(f[2]+f[3]-2*E[0])
            assert (num%24==0).all()
            return (left@(num//24))%3
        names=['s'+str(i) for i in range(len(D))]
        monomials=['1']+[v+'^2' for v in names]
        diagonals=[quadratic(v) for v in D]
        coeff=[left@b%3,*diagonals]
        for i,j in combinations(range(len(D)),2):
            monomials.append(names[i]+'*'+names[j])
            coeff.append((quadratic(D[i]+D[j])-diagonals[i]-diagonals[j])%3)
        eqs=[]
        for row in np.array(coeff).T:
            terms=[(str(c)+'*' if c!=1 else '')+m for c,m in zip(row,monomials) if c]
            if terms: eqs.append('+'.join(terms))
        assert eqs
        (dest/(str(ix).zfill(2)+'.in')).write_text(','.join(names)+'\n3\n'+',\n'.join(eqs)+'\n',newline='\n')
    print(len(planes),'jet ideals',flush=True)
if __name__=='__main__':
    generate()
