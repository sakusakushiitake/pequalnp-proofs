"""No symmetric three-dimensional permanent level at J over any cubic number field.

This CPU-only verification uses Python 3, NumPy and Numba. It handles the
unramified cubic 3-adic field, which is the remaining local case for cubic
number fields. The previous computations for residue F3, including total
ramification indices 2 and 3, are in
https://github.com/sakusakushiitake/pequalnp-proofs/tree/06e05713f0374757f72476aecaf1da4565c4231e/research/SymmetricRamification .
If a cubic number field has no degree-one residue place above 3, then 3
is inert. A place with residue F3 is already excluded for all possible
ramification indices. The inert place is excluded below. For quadratic
number fields see the earlier F9 computation.

Let r_k(X) be the sum of k-by-k subpermanents. The homogeneous degree-k
coefficient of per(J+X) is (4-k)! r_k. All r_k vanish on any candidate
in characteristic zero; reduce their integral equations separately.
Normalize a basis minor of minimal valuation to the identity to preserve
dimension on reduction. Use six symmetric edge coordinates followed by
three diagonal coordinates; r_1 recovers the last diagonal.

Every projective plane over F27 meets x01=0 in at least a line. Enumerate
all points of this hyperplane, normalizing the first nonzero coordinate
to one. For each prefix, 2r_2 is a monic quadratic in the third diagonal
when the first two diagonals are fixed: the last diagonal changes by the
negative of the third. We evaluate at zero and one to determine the other
two coefficients. A precomputed table tests all 27 potential roots.
The Frobenius conjugates of the first non-prime-field prefix entry are
processed together, then every reported point is restored. The final-pivot
case alone has diagonals 1,-1 and fails r_2. Count: 561780 points.

Every line has unique echelon rows p,h. The pivot of p is earlier than
that of h and p vanishes at the latter pivot. Test both rows and three
further points p+s*h with distinct nonzero s. Five projective points
detect homogeneous forms through degree four. This gives exactly 334 lines.
To extend a line, enforce the first derivatives of r_2,r_3,r_4 along it.
The two pivot coordinates of the extension vector are removed modulo the
line. Enumerate all projective directions in the remaining linear kernel.
Test z+s*p+t*h on a five-by-five grid, sufficient for degree four.
Deduplication gives exactly 224 planes. On an NVIDIA RTX 5070 Ti the point
and line arrays were separately reconstructed by GPU kernels using a
quadratic discriminant and different line samples. Both full arrays agree
byte for byte with this CPU program.

Write F27=F3[a]/(a^3-a-1); the polynomial is irreducible because it has
no root in F3. Its unramified lift modulo nine has the same presentation
over Z/9. The 224 planes split into eight orbits under S4 and Frobenius.
The unramified local field is Galois, so conjugation preserves liftability.
For all 31 coefficients in the three parameters of the plane, compute the
modulo-nine errors and the Jacobian in the 18 free chart entries. Every
orbit has inconsistent linear corrections. This leaves complex existence open.
"""
from itertools import combinations,permutations,product
from collections import Counter
import hashlib
import time
import numpy as np
from numba import njit,prange,set_num_threads,config
class Field:
    def __init__(self,d):
        q=3**d
        self.q=q
        a=np.empty((q,q),dtype=np.uint8)
        m=np.empty_like(a)
        for i in range(q):
            X=[i//(3**h)%3 for h in range(d)]
            for j in range(q):
                Y=[j//(3**h)%3 for h in range(d)]
                a[i,j]=sum((x+y)%3*3**v for v,(x,y) in enumerate(zip(X,Y)))
                v=np.convolve(X,Y)
                for k in range(len(v)-1,d-1,-1):
                    if d==2:v[k-2]-=v[k] # i^2=-1
                    elif d==3:
                        v[k-3]+=v[k];v[k-2]+=v[k] # i^3=i+1
                m[i,j]=sum(int(v[h]%3)*3**h for h in range(d))
        self.add=a;self.mul=m;self.neg=m[2]
        self.inv=np.array([0]+[int(np.flatnonzero(m[i]==1)[0]) for i in range(1,q)],dtype=np.uint8)
        sq=np.full(q,255,dtype=np.uint8)
        for i in range(q):sq[m[i,i]]=i
        self.sqrt=sq


field=Field(3)
add,mul,neg,inv=field.add,field.mul,field.neg,field.inv
pairs=list(combinations(range(4),2))+[(i,i) for i in range(4)]
index={c:k for k,c in enumerate(pairs)}
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
        n=27**(d-j-1);powers=27**np.arange(d-j-1)
        for st in range(0,n,32768):
            nums=np.arange(st,min(st+32768,n))
            a=np.zeros((len(nums),d),dtype=np.uint8)
            a[:,j]=1
            a[:,j+1:]=(nums[:,None]//powers)%27
            yield a
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
def cpu_evaluator(k):
    # Horner grouping directly from the integer counts of the rook monomials.
    # x01=0 on the fixed hyperplane, so terms containing it vanish.
    rem=[(c,list(ix)) for c,ix in terms[k] if 0 not in ix]
    def horner(rows):
        if not rows:return '0'
        if all(not s for c,s in rows):return str(sum(c for c,s in rows)%3)
        count=Counter(j for _,s in rows for j in s)
        var=count.most_common(1)[0][0]
        left=[];right=[]
        for c,s in rows:
            if var in s:
                s=s.copy();s.remove(var);left.append((c,s))
            else:right.append((c,s))
        f=horner(left)
        if f=='1':v='x['+str(var)+']'
        else:v='m[x['+str(var)+'],'+f+']'
        return 'a['+v+','+horner(right)+']' if right else v
    ns={}
    exec('def rook(x,a,m):\n    return '+horner(rem),ns)
    return njit(inline='always')(ns['rook'])

rook2,rook3,rook4=(cpu_evaluator(k) for k in (2,3,4))

@njit(parallel=True)
def batches(k,lo,n,div,a,m,frob,roots):
    q=len(a)
    out=np.zeros((n,6),dtype=np.uint64)
    for z in prange(n):
        v=np.zeros(10,dtype=np.int64)
        v[k]=1
        for j in range(k+1,8):v[j]=((lo+z)//div[j])%q
        orbit=1
        for j in range(1,8):
            t=v[j]
            if t<3:continue
            orbit=3 if t<min(frob[t],frob[frob[t]]) else 0
            break
        if not orbit:continue
        off=0
        for j in range(1,6):off=a[off,v[j]]
        b0=a[off,m[2,a[v[6],v[7]]]]
        v[9]=b0
        c=m[2,rook2(v,a,m)]
        v[8]=1;v[9]=a[b0,2]
        linear=a[m[2,rook2(v,a,m)],m[2,a[c,1]]]
        num=0
        for rt in roots[linear,c]:
            if rt==255:continue
            v[8]=rt;v[9]=a[b0,m[2,rt]]
            if rook3(v,a,m) or rook4(v,a,m):continue
            for g in range(orbit):
                val=np.uint64(0)
                for j in range(8,0,-1):
                    t=v[j]
                    if g>=1:t=frob[t]
                    if g==2:t=frob[t]
                    val=val*np.uint64(q)+np.uint64(t)
                out[z,num]=val
                num+=1
    return out

@njit(parallel=True)
def cpulines(piv,pts,P,H,offset,n,a,m):
    result=np.zeros(n,dtype=np.uint64)
    for t in prange(n):
        v=t+offset
        i=P[v%len(P)];j=H[v//len(P)]
        x=np.zeros(10,dtype=np.int64)
        ok=True
        for s in (1,4,5):
            for h in range(10):x[h]=a[pts[i,h],m[s,pts[j,h]]]
            if rook2(x,a,m) or rook3(x,a,m) or rook4(x,a,m):
                ok=False;break
        if ok:result[t]=((np.uint64(i)<<np.uint64(32))|np.uint64(j))+np.uint64(1)
    return result

def enumerate_cpu(F):
    q=F.q
    a,m=F.add,F.mul
    vals=np.arange(q);frob=m[vals,m[vals,vals]]
    roots=np.full((q,q,2),255,dtype=np.uint8)
    for b in range(q):
        for c in range(q):
            v=np.flatnonzero(a[m[vals,vals],a[m[b,vals],c]]==0)
            assert len(v)<=2
            roots[b,c,:len(v)]=v
    out=[];start=time.monotonic()
    chunk=1<<17
    for pivot in range(7,0,-1):
        div=np.array([q**max(j-pivot-1,0) for j in range(10)],dtype=np.int64)
        n=q**(7-pivot)
        for lo in range(0,n,chunk):
            h=batches(pivot,lo,min(chunk,n-lo),div,a,m,frob,roots)
            out.append(h[h!=0])
        print('CPU pivot',pivot,'points',sum(map(len,out)),'seconds',round(time.monotonic()-start,1),flush=True)
    X=np.sort(np.concatenate(out))
    assert len(X)==len(np.unique(X))==561780
    data=np.zeros((len(X),10),dtype=np.uint8)
    for j in range(1,9):data[:,j]=X//(q**(j-1))%q
    off=0;diag=0
    for j in range(6):off=a[off,data[:,j]]
    for j in range(6,9):diag=a[diag,data[:,j]]
    data[:,9]=a[off,m[2,diag]]
    piv=(data[:,:9]!=0).argmax(1)
    assert int((piv>=2).sum())==19956
    lines=[]
    for k in range(2,9):
        P=np.flatnonzero((piv<k)&(data[:,k]==0))
        H=np.flatnonzero(piv==k)
        total=len(P)*len(H)
        for lo in range(0,total,1<<19):
            L=cpulines(k,data,P,H,lo,min(1<<19,total-lo),a,m)
            lines.append(L[L!=0]-np.uint64(1))
        print('CPU later pivot',k,'lines',sum(map(len,lines)),flush=True)
    lines=np.sort(np.concatenate(lines))
    assert len(lines)==len(np.unique(lines))==334
    return X,data,np.column_stack((lines>>32,lines&0xffffffff)).astype(np.int32)

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

coeff_terms = make_coefficient_terms()
def ringmul(x,y):
    a,b,c=x[...,0],x[...,1],x[...,2]
    d,e,f=y[...,0],y[...,1],y[...,2]
    p3=b*f+c*e;p4=c*f
    return np.stack((a*d+p3,a*e+b*d+p3+p4,a*f+b*e+c*d+p4),axis=-1)%9

def equations(U):
    diag=-2*U[:,:,:6].sum(2)-U[:,:,6:].sum(2)
    U=np.concatenate((U,diag[:,:,None,:]),axis=2).reshape(len(U),30,3)%9
    allcols=[]
    for ex in coeff_terms.values():
        v=U[:,ex[:,0]]
        for j in range(1,ex.shape[1]):v=ringmul(v,U[:,ex[:,j]])
        allcols.append(v.sum(1)%9)
    return np.stack(allcols,axis=1)

def audit(F,B):
    ids={v.tobytes():i for i,v in enumerate(B)}
    ps=pairs;ix=index
    perms=[[ix[tuple(sorted((p[i],p[j])))] for i,j in ps[:-1]] for p in permutations(range(4))]
    vals=np.arange(27)
    frob=F.mul[vals,F.mul[vals,vals]]
    assert np.array_equal(frob[frob[frob[vals]]],vals)
    seen=set();stats=Counter();orbits=0
    for i,b in enumerate(B):
        if i in seen:continue
        orb=set()
        full=last(b)
        for p in perms:
            V,_=rref(full[:,p])
            for _ in range(3):
                orb.add(ids[V.tobytes()])
                V=frob[V]
        assert not orb&seen;seen.update(orb);orbits+=1
        _,piv=rref(b)
        free=[(i,j) for i in range(3) for j in range(9) if j not in piv]
        base=np.stack((b%3,b//3%3,b//9),axis=-1).astype(np.int64)
        U=np.broadcast_to(base,(19,3,9,3)).copy()
        for z,(i,j) in enumerate(free):U[z+1,i,j,0]+=3
        eq=equations(U)
        assert (eq%3==0).all()
        digits=eq//3
        def enc(ds):return (ds%3)@np.array([1,3,9],dtype=np.int64)
        A=enc(digits[1:]-digits[0]).T
        _,p=rref(np.column_stack((A,enc(-digits[0]))))
        stats[len(p)-(18 in p),18 not in p]+=len(orb)
    print('mod-nine lift, ranks',sorted(stats.items()),'orbits',orbits,flush=True)
    assert len(seen)==len(B)
    return stats,orbits


def verify():
    set_num_threads(min(10,config.NUMBA_NUM_THREADS))
    packed,X,lines=enumerate_cpu(field)
    def digest(a):return hashlib.sha256(a.tobytes()).hexdigest()
    assert digest(packed.astype('<u8'))=='429e2b22569bf5bdcea967d258b40c33a818ceb651d6b1323452b8841ab3124a'
    assert digest(lines.astype('<i4'))=='1811d134f804bb8f969b4971ba8be22e70f5452669ffdefe49ba9f62bd8a6255'
    found=set()
    for line in lines:
        extra,_=extensions(X[:,:9],line)
        found.update(extra)
    B=np.array([np.frombuffer(v,dtype=np.uint8).reshape(3,9) for v in sorted(found)])
    assert len(B)==224 and (B<3).all(axis=(1,2)).sum()==32
    assert digest(B)=='c7d9681f71de6ea8b5083c7913d9ecd0a81abfc8090e1e8deefa6c986c8d9198'
    stats,orbits=audit(field,B)
    assert orbits==8 and stats=={(9,False):4,(12,False):112,(14,False):108}
    print('All 224 planes are obstructed modulo nine over the unramified cubic 3-adic field.')

if __name__=='__main__':verify()
