"""Compute tangent spaces and first lift obstructions on each F3 plane."""
from itertools import permutations,combinations,product
from collections import defaultdict,Counter
from pathlib import Path
import numpy as np
import json
from symmetric_three import verify

cells=list(combinations(range(4),2))+[(i,i) for i in range(4)]
index={c:k for k,c in enumerate(cells)}
rows=defaultdict(list)
for k in (2,3,4):
    for rr in combinations(range(4),k):
        for cc in permutations(range(4),k):
            addresses=[index[tuple(sorted(p))] for p in zip(rr,cc)]
            for axes in product(range(3),repeat=k):
                ex=tuple(axes.count(i) for i in range(3))
                rows[ex].append([10*a+b for a,b in zip(axes,addresses)])
terms={ex:np.asarray(inds) for ex,inds in sorted(rows.items())}

def equations(B):
    B=np.asarray(B,dtype=np.int64)
    D=np.concatenate([B,(-2*B[:,:,:6].sum(2)-B[:,:,6:].sum(2))[:,:,None]],axis=2).reshape(len(B),30)
    return np.column_stack([D[:,idx].prod(axis=2).sum(axis=1) for idx in terms.values()])

def rref(matrix,p=3):
    A=np.array(matrix,dtype=np.int64)%p
    piv=[]
    for j in range(A.shape[1]):
        k=len(piv)
        nz=np.flatnonzero(A[k:,j])
        if len(nz)==0: continue
        h=k+int(nz[0])
        A[[k,h]]=A[[h,k]]
        A[k]=A[k]*pow(int(A[k,j]),-1,p)%p
        for i in range(len(A)):
            if i!=k: A[i]=(A[i]-A[i,j]*A[k])%p
        piv.append(j)
    return A,piv

def audit():
    planes=verify(return_planes=True)
    report=[]
    for plane in planes:
        U,piv=rref(plane)
        B=U[:3]
        assert len(piv)==3
        free=[(i,j) for i in range(3) for j in range(9) if j not in piv]
        versions=[B]
        for i,j in free:
            Y=B.copy()
            Y[i,j]+=3
            versions.append(Y)
        E=equations(versions)
        assert E.shape==(19,31) and (E%3==0).all()
        A=((E[1:]-E[:1])//3).T%3
        b=(-E[0]//3)%3
        _,r=rref(A)
        _,aug=rref(np.column_stack((A,b)))
        report.append(dict(pivots=piv,basis=B.tolist(),rank=len(r),tangent=18-len(r),lift=len(r)==len(aug)))
    print(dict(Counter((e['tangent'],e['lift']) for e in report)))
    Path(__file__).with_name('symmetric-hensel-three.json').write_text(json.dumps(report))

if __name__=='__main__':
    audit()
