"""Obstruction modulo 5 to a rational 3-space of symmetric 4-by-4 matrices
on which per(J+X)=24. Run with Python 3 and NumPy.

For a rational 3-space, choose a nonzero 3-by-3 minor of its basis matrix
with smallest 5-adic valuation. Normalize these three rows to the identity.
By Cramer's rule every entry of the resulting basis is integral at 5.
Reduction preserves rank and the integer polynomial identities for the level
condition. Thus a rational 3-space would give a projective plane over F_5.
"""
from itertools import combinations, permutations
import numpy as np


def enumerate_points():
    # Pack the six upper off-diagonal entries followed by the first three
    # diagonal entries. The last diagonal follows from the linear coefficient.
    cells=list(combinations(range(4),2))+[(i,i) for i in range(4)]
    offsets={c:i for i,c in enumerate(cells)}
    terms={}
    for d in (2,3,4):
        terms[d]=[[offsets[tuple(sorted((i,j)))] for i,j in zip(rr,cc)]
                  for rr in combinations(range(4),d) for cc in permutations(range(4),d)]
    powers=5**np.arange(9,dtype=np.int64)
    out=[]
    # Last nonzero digit normalized to one. Each nonzero projective point
    # in the sum-zero hyperplane has exactly one such representative.
    for j in range(9):
        for lo in range(0,5**j,32768):
            nums=np.arange(lo,min(lo+32768,5**j),dtype=np.int64)+5**j
            x=np.zeros((len(nums),10),dtype=np.int64)
            x[:,:9]=(nums[:,None]//powers)%5
            x[:,9]=(-2*x[:,:6].sum(axis=1)-x[:,6:9].sum(axis=1))%5
            for d in (2,3,4):
                coeff=np.zeros(len(x),dtype=np.int64)
                for ii in terms[d]:
                    v=x[:,ii[0]].copy()
                    for k in ii[1:]:
                        v*=x[:,k]
                    coeff+=v
                x=x[coeff%5==0]
            out.extend(x[:,:9].tolist())
    return np.array(out,dtype=np.int64)


def verify():
    pts=enumerate_points()
    n=len(pts)
    powers=5**np.arange(9,dtype=np.int64)
    valid=np.zeros(5**9,dtype=bool)
    for a in range(1,5):
        valid[((a*pts)%5)@powers]=True
    assert valid.sum()==4*n
    # Each projective line determined by two points has four further points.
    # Membership in the affine cone lets us check them without normalizing.
    adj=[set() for _ in pts]
    for i,x in enumerate(pts):
        ids=np.arange(i+1,n)
        for a in range(1,5):
            ids=ids[valid[((x+a*pts[ids])%5)@powers]]
        for j in ids:
            adj[i].add(int(j))
            adj[j].add(i)
    pairs=sum(map(len,adj))//2
    assert pairs%15==0
    # A projective plane over F_5 has 31 points, and all joining lines are
    # contained. Its points survive every deletion of a vertex of degree <30.
    alive=set(range(n))
    sizes=[n]
    while True:
        keep={i for i in alive if len(adj[i]&alive)>=30}
        if keep==alive:
            break
        alive=keep
        sizes.append(len(alive))
    result=dict(points=n,lines=pairs//15,pruning=sizes)
    print(result)
    assert not alive, "remaining points need further tests"
    return result


if __name__=='__main__':
    verify()
