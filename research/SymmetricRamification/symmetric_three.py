"""Check rational planes in the degree-by-degree special fibre at 3."""
from itertools import combinations,permutations
import numpy as np
from pathlib import Path
import json

def verify(return_planes=False):
    pairs=list(combinations(range(4),2))+[(i,i) for i in range(4)]
    index={q:i for i,q in enumerate(pairs)}
    terms={}
    for k in (2,3,4):
        terms[k]=[[index[tuple(sorted(e))] for e in zip(rows,cols)]
                  for rows in combinations(range(4),k) for cols in permutations(range(4),k)]
    powers=3**np.arange(9)
    data=np.arange(1,3**9)[:,None]//powers%3
    data=data[data[np.arange(len(data)),(data!=0).argmax(axis=1)]==1]
    X=np.column_stack((data,-2*data[:,:6].sum(axis=1)-data[:,6:].sum(axis=1)))%3
    for k,products in terms.items():
        X=X[sum(np.prod(X[:,t],axis=1) for t in products)%3==0]
    P=X[:,:9]
    valid=np.zeros(3**9,dtype=np.int32)-1
    for a in (1,2):
        valid[(a*P%3)@powers]=np.arange(len(P))
    grad=np.zeros_like(X)
    for term in terms[4]:
        for i,j in enumerate(term):
            grad[:,j]+=np.prod(X[:,term[:i]+term[i+1:]],axis=1)
    adj=[set() for _ in P]
    lines=set()
    for i,x in enumerate(P):
        others=np.arange(i+1,len(P))
        plus=valid[((x+P[others])%3)@powers]
        minus=valid[((x-P[others])%3)@powers]
        # A quartic on a projective F3 line with all four points zero can
        # only be a scalar multiple of s^3*t-s*t^3. Its t-linear term
        # at (1,0) is the scalar. Lower homogeneous degrees have no ambiguity.
        mask=(plus>=0)&(minus>=0)&((X[others]@grad[i])%3==0)
        for j,a,b in zip(others[mask],plus[mask],minus[mask]):
            line=tuple(sorted(map(int,(i,j,a,b))))
            if line not in lines:
                lines.add(line)
                for v in line: adj[v].update(line)
    planes=set()
    for line in lines:
        for i in set.intersection(*(adj[j] for j in line))-set(line):
            pts=set(line)|{i}
            for j in line:
                pts.update(int(valid[((P[i]+a*P[j])%3)@powers]) for a in (1,2))
            assert len(pts)==13 and -1 not in pts
            if all(pts<=adj[j] for j in pts):
                planes.add(tuple(sorted(pts)))
    print('p=3',len(P),'points',len(lines),'geometric lines over F3',len(planes),'planes',flush=True)
    assert (len(P),len(lines),len(planes))==(388,488,32)
    if planes and not return_planes:
        print('one plane',P[list(next(iter(planes)))].tolist(),flush=True)
    if return_planes:
        return [P[list(v)] for v in sorted(planes)]
    return len(P),len(lines),len(planes)

if __name__=='__main__':
    result=verify()
    Path(__file__).with_name('symmetric-three-result.json').write_text(json.dumps(result))
