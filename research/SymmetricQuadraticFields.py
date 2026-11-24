"""No symmetric three-plane for per(J+X)=24 over a quadratic number field.

Run this file with Python 3 and NumPy. It verifies the unramified quadratic
case at 3. The split and ramified cases are proved in the companion package
https://github.com/sakusakushiitake/pequalnp-proofs/tree/06e05713f0374757f72476aecaf1da4565c4231e/research/SymmetricRamification

Write r_k for the sum of k-by-k subpermanents. On a characteristic-zero
linear space the homogeneous coefficients of per(J+X) are (4-k)! r_k.
Hence the four r_k vanish individually, and the integer equations r_k=0
stay valid in an integral chart. Choose a basis minor of least valuation
and normalize it to the identity. This gives a rank-three special fiber.

Use the six upper off-diagonals followed by three diagonals; r_1 fixes the
last diagonal. Every projective plane in P^8 meets x01=0 in at least a
line. Every such line meets x02=0. The point and line lists below exhaust
these intersections over F_9. For each line the three gradients on its
points give necessary linear conditions on every extension direction.
Killing the two pivot coordinates of the line chooses a representative in
the quotient. Enumerate all projective directions in that subspace and
test z+s*a+t*b on a 5-by-5 grid of distinct field elements. Because each
degree is at most four, vanishing on the grid makes the restriction to the
plane identically zero. The charts are deduplicated by reduced row form.

The 6592 planes have 164 orbits under S4 and field conjugation. At an
orbit representative B normalize a unit minor and use the 18 free entries.
Compute all 31 coefficients F(B) over Gaussian integers modulo nine.
Their linearization asks whether A*u = -F(B)/3 in F_9, where the columns
of A are (F(B+3E_j)-F(B))/3. This covers every modulo-nine lift because
3 is a uniformizer of the unramified quadratic extension Q_3(i).
The augmented rank exceeds the coefficient rank in every orbit. The
inconsistent systems stay inconsistent after extending the residue field.
The result still leaves the complex existence problem open.
"""
from collections import Counter
from itertools import combinations,permutations
from pathlib import Path
import json
import numpy as np

pairs=list(combinations(range(4),2))+[(i,i) for i in range(4)]
index={c:k for k,c in enumerate(pairs)}
add=np.empty((9,9),dtype=np.uint8)
mul=np.empty_like(add)
for i in range(9):
    a,b=i%3,i//3
    for j in range(9):
        c,d=j%3,j//3
        add[i,j]=(a+c)%3+3*((b+d)%3)
        mul[i,j]=(a*c-b*d)%3+3*((a*d+b*c)%3)
neg=mul[2]
inv=np.array([0]+[int(np.flatnonzero(mul[i]==1)[0]) for i in range(1,9)],dtype=np.uint8)
terms={}
for k in (2,3,4):
    raw=Counter(tuple(sorted(index[tuple(sorted(e))] for e in zip(rr,cc)))
                for rr in combinations(range(4),k) for cc in permutations(range(4),k))
    terms[k]=[(v%3,ex) for ex,v in raw.items() if v%3]

def sumf(xs):
    a=0
    for b in xs:a=add[a,b]
    return a
def last(X):
    # -2=1 in F3.
    return np.column_stack((X,add[sumf(X[:,k] for k in range(6)),neg[sumf(X[:,k] for k in range(6,9))]]))
def value(X,k):
    if k==2:
        rows=[sumf(X[:,index[tuple(sorted((i,j)))]] for j in range(4)) for i in range(4)]
        # 2r2 = -2 sum row_i^2 + sum_{ij} X_ij^2 in the sum-zero hyperplane.
        return add[sumf(mul[r,r] for r in rows),add[neg[sumf(mul[X[:,i],X[:,i]] for i in range(6))],
                                                      sumf(mul[X[:,i],X[:,i]] for i in range(6,10))]]
    total=np.zeros(len(X),dtype=np.uint8)
    for c,idx in terms[k]:
        a=X[:,idx[0]]
        for j in idx[1:]:a=mul[a,X[:,j]]
        total=add[total,a if c==1 else neg[a]]
    return total
def good(X):
    ids=np.arange(len(X))
    for k in (2,3,4):
        if not len(ids):break
        ids=ids[value(X[ids],k)==0]
    return ids
def projective(d):
    for j in range(d):
        n=9**(d-j-1);powers=9**np.arange(d-j-1)
        for st in range(0,n,32768):
            nums=np.arange(st,min(st+32768,n))
            a=np.zeros((len(nums),d),dtype=np.uint8)
            a[:,j]=1
            a[:,j+1:]=(nums[:,None]//powers)%9
            yield a
def points():
    pts=[]
    for a in projective(8):
        a=np.column_stack((np.zeros(len(a),dtype=np.uint8),a))
        pts.append(a[good(last(a))])
    return np.vstack(pts)
def line_list(P):
    powers=9**np.arange(8)
    ids=np.full(9**8,-1,dtype=np.int32)
    seq=np.arange(len(P),dtype=np.int32)
    for t in range(1,9):ids[mul[t,P[:,1:]]@powers]=seq
    lines=set()
    for h in np.flatnonzero(P[:,1]==0):
        active=seq[seq!=h]
        for t in range(1,9):
            active=active[ids[add[P[active,1:],mul[t,P[h,1:]]]@powers]>=0]
            if not len(active):break
        for j in active:
            if j<h and P[j,1]==0:continue
            L=[h,*[int(ids[add[P[j,1:],mul[t,P[h,1:]]]@powers]) for t in range(9)]]
            assert len(set(L))==10 and min(L)>=0
            lines.add(tuple(sorted(map(int,L))))
    return sorted(lines)
def rref(M):
    A=np.asarray(M,dtype=np.uint8).copy()
    piv=[]
    for j in range(A.shape[1]):
        k=len(piv)
        nz=np.flatnonzero(A[k:,j])
        if not len(nz):continue
        h=k+int(nz[0]);A[[k,h]]=A[[h,k]]
        A[k]=mul[inv[A[k,j]],A[k]]
        factors=A[:,j].copy();factors[k]=0
        A=add[A,neg[mul[factors[:,None],A[k]]]]
        piv.append(j)
    return A,piv
def ker(M):
    A,piv=rref(M)
    free=[j for j in range(A.shape[1]) if j not in piv]
    K=np.zeros((len(free),A.shape[1]),dtype=np.uint8)
    for i,j in enumerate(free):
        K[i,j]=1
        for k,col in enumerate(piv):K[i,col]=neg[A[k,j]]
    return K
def gradient(U,k):
    G=np.zeros((len(U),10),dtype=np.uint8)
    for c,idx in terms[k]:
        for q,j in enumerate(idx):
            if q and idx[q-1]==j:continue
            e=(c*idx.count(j))%3
            if not e:continue
            v=e
            for b,l in enumerate(idx):
                if b!=q:v=mul[v,U[:,l]]
            G[:,j]=add[G[:,j],v]
    return np.column_stack(([add[G[:,i],G[:,9]] for i in range(6)]+[add[G[:,i],neg[G[:,9]]] for i in range(6,9)]))
def extensions(P,line):
    X,pc=rref(P[list(line[:2])])
    assert len(pc)==2
    a,b=X
    samples=last(np.array([add[a,mul[t,b]] for t in (0,1,2,3)]+[b]))
    E=np.eye(9,dtype=np.uint8)[pc]
    K=ker(np.vstack([E,*[gradient(samples,k) for k in (2,3,4)]]))
    planes=[]
    for V in projective(len(K)):
        Z=sumf(mul[V[:,i,None],K[i]] for i in range(len(K)))
        for s,t in [(s,t) for s in range(5) for t in range(5)]:
            Z=Z[good(last(add[Z,add[mul[s,a],mul[t,b]]]))]
            if not len(Z):break
        for v in Z:
            R,piv=rref(np.vstack((a,b,v)))
            assert len(piv)==3
            planes.append(R.tobytes())
    return planes,len(K)
from itertools import product

def make_coefficient_terms():
    accum = {}
    for k in (2, 3, 4):
        for rr in combinations(range(4), k):
            for cc in permutations(range(4), k):
                addresses = [index[tuple(sorted(e))] for e in zip(rr, cc)]
                for axes in product(range(3), repeat=k):
                    degree = tuple(axes.count(i) for i in range(3))
                    accum.setdefault(degree, []).append([10*a+b for a,b in zip(axes,addresses)])
    assert len(accum) == 31
    return {d: np.asarray(v) for d,v in sorted(accum.items())}

coefficient_terms = make_coefficient_terms()
conj = np.array([a % 3 + 3 * (-(a // 3) % 3) for a in range(9)], dtype=np.uint8)
perms = [[index[tuple(sorted((p[i], p[j])))] for i, j in pairs[:-1]]
         for p in permutations(range(4))]

def orbits(bases):
    ids = {b.tobytes(): i for i,b in enumerate(bases)}
    seen = set()
    for i,b in enumerate(bases):
        if i in seen:
            continue
        d = last(b)
        orbit = set()
        for perm in perms:
            R, _ = rref(d[:,perm])
            orbit.update((ids[R.tobytes()], ids[conj[R].tobytes()]))
        assert not orbit.intersection(seen)
        seen.update(orbit)
        yield i, len(orbit)
    assert len(seen) == len(bases)

def coefficients(matrices):
    # Exact Gaussian integers. Reduce the eliminated coordinate modulo 9 before
    # multiplying. The largest coefficient sum is at most 4^4 * 24 * (8+8)^4,
    # far below the integer precision of binary64.
    real = matrices.real.astype(np.int64)
    imag = matrices.imag.astype(np.int64)
    def extend(x):
        diagonal = -2 * x[:,:,:6].sum(2) - x[:,:,6:].sum(2)
        return np.concatenate([x,diagonal[:,:,None]], axis=2).reshape(len(x),30) % 9
    d = extend(real) + 1j * extend(imag)
    return np.column_stack([d[:,ix].prod(axis=2).sum(axis=1) for ix in coefficient_terms.values()])

def encode(real,imag):
    return (real % 3 + 3 * (imag % 3)).astype(np.uint8)

def linearize(b):
    _, piv = rref(b)
    free = [(i,j) for i in range(3) for j in range(9) if j not in piv]
    B = b % 3 + 1j * (b // 3)
    U = np.broadcast_to(B,(19,3,9)).copy()
    for a,(i,j) in enumerate(free):
        U[a+1,i,j] += 3
    F = coefficients(U)
    real, imag = F.real.astype(np.int64), F.imag.astype(np.int64)
    assert np.all(real % 3 == 0) and np.all(imag % 3 == 0)
    real //= 3
    imag //= 3
    A = encode(real[1:]-real[0],imag[1:]-imag[0]).T
    c = encode(-real[0],-imag[0])
    return free,A,c


def verify():
    # Check the fast quadratic zero test against the definition as a rook sum.
    rg = np.random.default_rng(231)
    x = last(rg.integers(0,9,size=(4096,9),dtype=np.uint8))
    raw2 = sumf(mul[c,mul[x[:,i],x[:,j]]] for c,(i,j) in terms[2])
    assert np.array_equal(value(x,2),mul[2,raw2])
    P = points()
    assert (len(P), int((P[:,1] == 0).sum())) == (8880,1232)
    lines = line_list(P)
    assert len(lines) == 918
    raw = set()
    for line in lines:
        found, _ = extensions(P,line)
        raw.update(found)
    bases = [np.frombuffer(k,dtype=np.uint8).reshape(3,9) for k in sorted(raw)]
    assert len(bases) == 6592 and sum(bool((b<3).all()) for b in bases) == 32
    stats = Counter()
    number = 0
    for i, size in orbits(bases):
        _, A, c = linearize(bases[i])
        R,piv = rref(np.column_stack((A,c)))
        assert piv[-1] == 18 and (R[len(piv)-1,:18] == 0).all()
        stats[len(piv)-1] += size
        number += 1
    assert number == 164 and stats == {9:28,12:24,14:92,15:6448}
    print("8880 hyperplane points, 918 lines, 6592 planes, 164 orbits.")
    print("No modulo-nine lift in the unramified quadratic extension; ranks", sorted(stats.items()))

if __name__ == '__main__':
    verify()
