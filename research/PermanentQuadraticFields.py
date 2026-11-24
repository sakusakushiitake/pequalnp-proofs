"""No six-dimensional level space for per(I+J+X)=65 over any quadratic number field.

Run with Python 3 and NumPy. This script exhausts all six ramified quadratic
extensions of Q2 by testing the necessary integral equations modulo pi^5.
The previously verified unramified obstruction and its nilpotent-space proof
are supplied by the companion program:
https://github.com/sakusakushiitake/pequalnp-proofs/blob/872578d2c53cd41df1d526607b0455325ba4e1bc/research/PermanentUnramified.py

Put A=I+J of order four. On reduction modulo the maximal ideal at two,
A is invertible and the permanent agrees with the determinant. Normalizing
a basis minor of least valuation preserves dimension. Thus A^{-1} times
the six-dimensional direction space is a maximal space of nilpotent
matrices. Gerstenhaber's equality classification gives one full flag in
F2^4; see https://arxiv.org/abs/1210.4951 . Enumerate all 315 flags, then
use simultaneous vertex permutations and transpose to obtain 17 orbits.

The equations F(B) for a Grassmann chart B include all nonconstant
coefficients of per(A+sum_j x_j B_j)-65. Extra necessary integer equations
come from projection to singular subspaces of codimension at most six.
For an r by (5-r) rectangle, setting all entries to zero precludes every
perfect matching. Thus the projection of the direction space to this
rectangle cannot be surjective: it would translate A to a singular matrix.
In a two-row/two-column block one may likewise set the other four entries
of these rows to zero and impose two linear relations making the block
permanent zero. Use both rulings of its quadric, represented by
(a-s*b,c+s*d) and (a-s*c,b+s*d) for block [[a,b],[c,d]], and their
transposes. The six-by-six determinant of the projected directions then
vanishes as a polynomial in s. Keep its three integer coefficients, using
the evaluations at 0,1,-1 before reduction. This does not assume s lies
in the residue field.

The chart has 60 free entries. Let P=F'(B) mod 2, K=ker P, and L a matrix
whose rows span the left kernel. Every lift has the form
B+pi*D+pi^2*E+pi^3*G+pi^4*H modulo pi^5. The first digit D ranges over
K. The rings used have pi^2=2u+2h*pi for (u,h)=(1,0),(-1,0),(5,0),
(-5,0),(-1,1),(-3,1). These correspond to sqrt(2), sqrt(-2), sqrt(10),
sqrt(-10), 1+sqrt(-1), 1+sqrt(-5). Together with the unramified extension
and the split case they cover every completion of a quadratic number field
at two (Q2 square classes are represented by 1,-1,2,-2,5,-5,10,-10).

Write Q and C for the quadratic and cubic Hasse coefficients of F at B,
and P_Z for its integer derivative. At order two solve
P E = F(B)/2 + Q(D) mod 2. For each accepted D this gives E=e+K*t.
At order three the condition before G is
P_Z(D)/2 + C(D) + Q(D+E)-Q(D)-Q(E) + h F(B)/2 mod 2.
Indeed 2/pi^2=1/(u+h*pi)=1+h*pi modulo pi^2. Project by L and solve
linearly in t. The program computes Hasse coefficients with symmetric
integer differences; every division used has an exact integer numerator.

For order four the actual ring of each extension is used. For each
remaining affine family E(z), the order-three condition yields a particular
G(z) affine in z. Changing G by a vector in K changes the next projected
obstruction by L times the polarization of Q(D) in that vector. Project
away this image as well as the new correction P H. The remaining function
of the binary parameters z has degree at most two (their entries first
occur at order two). Evaluate it on zero, each unit and each pair to
reconstruct its full Boolean polynomial, then test all z. No candidate
survives. Ring elements are represented as integer pairs a+b*pi modulo
powers of two; the precision retained exceeds what five digits need.

The result excludes the rational and quadratic number fields. No assertion
about the full complex six-space existence question follows from this test.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json
import numpy as np

mons=[m for k in range(5) for m in combinations_with_replacement(range(6),k)]
pos={m:i for i,m in enumerate(mons)}
short=len([m for m in mons if len(m)<4])
shift=np.array([[pos[tuple(sorted((v,)+m))] for m in mons[:short]] for v in range(6)])
base=np.ones((4,4),dtype=np.int64)+np.eye(4,dtype=np.int64)

def flags(prefix=(),span=frozenset([0])):
    if len(prefix)==4:
        yield prefix
        return
    seen=set(span)
    for v in range(1,16):
        if v in seen:
            continue
        coset={u^v for u in span}
        seen.update(coset)
        yield from flags(prefix+(v,),span|coset)

def reduce2(M):
    M=np.array(M,dtype=np.uint8)%2
    p=[]
    for j in range(M.shape[1]):
        k=len(p)
        idx=np.flatnonzero(M[k:,j])
        if not len(idx):continue
        h=k+int(idx[0])
        M[[k,h]]=M[[h,k]]
        rows=M[:,j].copy().astype(bool)
        rows[k]=False
        M[rows]^=M[k]
        p.append(j)
    return M,p

def basis(flag):
    U=np.array([[(v>>i)&1 for v in flag] for i in range(4)],dtype=np.uint8)
    R,p=reduce2(np.column_stack((U,np.eye(4,dtype=np.uint8))))
    assert p==list(range(4))
    inv=R[:,4:]
    assert np.array_equal((U@inv)%2,np.eye(4))
    AU=base@U%2
    return reduce2([np.outer(AU[:,i],inv[j]).reshape(16) for i,j in combinations(range(4),2)])

def coeffs(B):
    B=B.reshape(6,4,4)
    one=np.zeros(len(mons),dtype=np.int64)
    one[0]=1
    polys={((),()):one}
    all4=tuple(range(4))
    for k in range(1,5):
        parts=list(combinations(all4,k))
        for rows in parts:
            for cols in parts:
                v=np.zeros(len(mons),dtype=np.int64)
                i=rows[0]
                for a,j in enumerate(cols):
                    q=polys[rows[1:],cols[:a]+cols[a+1:]]
                    v+=base[i,j]*q
                    for z in np.flatnonzero(B[:,i,j]):
                        v[shift[z]]+=int(B[z,i,j])*q[:short]
                polys[rows,cols]=v
    F=polys[all4,all4].copy()
    F[0]-=65
    cof=[polys[all4[:i]+all4[i+1:],all4[:j]+all4[j+1:]] for i in all4 for j in all4]
    return F,cof


from itertools import permutations
def ker2(A):
    R,p=reduce2(A)
    f=[j for j in range(A.shape[1]) if j not in p]
    K=np.zeros((len(f),A.shape[1]),dtype=np.int64)
    for h,j in enumerate(f):
        K[h,j]=1
        K[h,p]=R[:len(p),j]
    return K

def orbit(B):
    out=set()
    for p in permutations(range(4)):
        M=B.reshape(6,4,4)[:,p,:][:,:,p]
        for Y in [M,M.transpose(0,2,1)]:
            out.add(reduce2(Y.reshape(6,16))[0].tobytes())
    return out

E=np.eye(16,dtype=np.int64).reshape(4,4,16)
four=[]
six=[]
for r in (1,2,3,4):
    for rows in combinations(range(4),r):
        for cols in combinations(range(4),5-r):
            mat=[E[i,j] for i in rows for j in cols]
            (six if len(mat)==6 else four).append(mat)
both=[]
for T in [E,E.transpose(1,0,2)]:
    for a,b in combinations(range(4),2):
        for x,y in combinations(range(4),2):
            zeros=[T[i,j] for i in (a,b) for j in range(4) if j not in (x,y)]
            # Both rulings of the 2-by-2 permanent quadric.
            for pair in [(T[a,x],T[a,y],T[b,x],T[b,y]),
                         (T[a,x],T[b,x],T[a,y],T[b,y])]:
                u,v,z,t=pair
                for s in (0,1,-1):
                    both.append(zeros+[u-s*v,z+s*t])
F4=np.array(four).transpose(0,2,1)
F6=np.array(six+both).transpose(0,2,1)
minorrows=np.array(list(combinations(range(6),4)))

def dets(A):
    n=A.shape[-1]
    dp={0:np.ones(A.shape[:-2],dtype=np.int64)}
    for mask in range(1,1<<n):
        cols=[j for j in range(n) if mask>>j&1]
        r=len(cols)-1
        dp[mask]=sum(((-1)**(r+h))*A[...,r,j]*dp[mask^(1<<j)] for h,j in enumerate(cols))
    return dp[(1<<n)-1]

def equations(B):
    P,_=coeffs(B)
    B=B.astype(np.int64)
    small=dets((B@F4)[:,minorrows,:]).ravel()
    full=dets(B@F6)
    family=full[len(six):].reshape(-1,3)
    # Restricting the six-by-six determinant in the ruling parameter gives
    # an integer polynomial of degree at most two. Its three coefficients
    # vanish in characteristic zero. Retain them individually before reduction.
    assert ((family[:,1]-family[:,2])%2==0).all()
    mid=(family[:,1]-family[:,2])//2
    top=family[:,1]-family[:,0]-mid
    return np.concatenate((P,small,full[:len(six)],family[:,0],mid,top))

def model(f):
    B,p=basis(f)
    B=B.astype(np.int64)
    free=[(k,j) for j in range(16) if j not in p for k in range(6)]
    moves=np.zeros((60,6,16),dtype=np.int64)
    for h,(k,j) in enumerate(free):moves[h,k,j]=1
    F=equations(B)
    assert (F%2==0).all()
    A=np.array([((equations(B+2*d)-F)//2)%2 for d in moves]).T
    # Dimension-six flag motion survives every added determinant identity.
    K=ker2(A)
    assert len(K)>=6
    left=ker2(A.T)
    D=(K@moves.reshape(60,96)).reshape(-1,6,16)
    return B,F,A,left,D,moves

def jets(f,root):
    B,F,A,left,D,_=model(f)
    def q(v):
        raw=equations(B+2*v)+equations(B-2*v)-2*F
        assert (raw%8==0).all()
        return left@(raw//8)%2
    diag=[q(v) for v in D]
    pairs=list(combinations(range(len(D)),2))
    co=np.array([left@(F//2)%2,*diag,*[(q(D[i]+D[j])-diag[i]-diag[j])%2 for i,j in pairs]]).T
    # Row reduction also detects an identically contradictory equation.
    rr,p=reduce2(co[:,list(range(1,co.shape[1]))+[0]])
    impossible=(co.shape[1]-1 in p)
    mon=[0,*[1<<i for i in range(len(D))],*[(1<<i)|(1<<j) for i,j in pairs]]
    masks=np.arange(1<<len(D),dtype=np.uint32)
    for row in co:
        if not len(masks):break
        y=np.zeros(len(masks),dtype=np.uint8)
        for j in np.flatnonzero(row):y^=(masks&mon[j])==mon[j]
        masks=masks[~y.astype(bool)]
    tag='-'.join(map(str,f))
    np.save(root/(tag+'-masks.npy'),masks)
    return len(D),impossible,len(masks)

def linear(A,b):
    R,p=reduce2(np.column_stack((A,b)))
    n=A.shape[1]
    if n in p:return None
    v=np.zeros(n,dtype=np.int64)
    v[p]=R[:len(p),-1]
    assert np.array_equal(A@v%2,b%2)
    return v

def third(flag,src):
    B,F,A,L,D,moves=model(flag)
    K=ker2(A)
    assert np.array_equal(D,(K@moves.reshape(60,96)).reshape(-1,6,16))
    tag='-'.join(map(str,flag))
    masks=np.load(src/(tag+'-masks.npy'))
    small=[equations(B+2*v) for v in moves]
    H=np.zeros((len(D),len(moves),len(F)),dtype=np.uint8)
    for i,v in enumerate(D):
        f=equations(B+2*v)
        for j,e in enumerate(moves):
            diff=equations(B+2*(v+e))-f-small[j]+F
            assert (diff%4==0).all()
            H[i,j]=(diff//4)%2
    results=[[],[]]
    for m in masks:
        sel=np.array([(int(m)>>i)&1 for i in range(len(D))],dtype=np.int64)
        V=(sel@D.reshape(len(D),96)).reshape(6,16)
        hm=H[sel.astype(bool)].sum(0,dtype=np.int64)%2
        p2,m2,p4,m4=(equations(B+k*V) for k in (2,-2,4,-4))
        q2=(p2+m2-2*F)//8
        e=linear(A,(F//2+q2)%2)
        assert e is not None
        v1=(p4-m4)//8
        q3=((p2-m2)//4-v1)//4
        assert (v1%2==0).all()
        delta=(L@hm.T@K.T)%2
        fo=v1//2+q3+e@hm
        for h in (0,1):
            b=(L@(fo+h*(F//2)))%2
            t=linear(delta,b)
            if t is None:continue
            T=ker2(delta)
            results[h].append(dict(mask=int(m),e=e.tolist(),t=t.tolist(),kernel=T.tolist()))
    (src/(tag+'-third.json')).write_text(json.dumps(results))
    print(flag,'first masks',len(masks),'eligible for order four',
          [(len(rs),sum(2**len(r['kernel']) for r in rs)) for rs in results],flush=True)

mod=512
def mul(x,y,u,h):
    a,b=x[...,0],x[...,1]
    c,d=y[...,0],y[...,1]
    bd=b*d
    return np.stack(((a*c+2*u*bd)%mod,(a*d+b*c+2*h*bd)%mod),axis=-1)

def permanent_coeff(B,u,h):
    B=B.reshape(6,4,4,2)
    one=np.zeros((len(mons),2),dtype=np.int64)
    one[0,0]=1
    all4=tuple(range(4))
    polys={((),()):one}
    for k in range(1,5):
        parts=list(combinations(all4,k))
        for rows in parts:
            for cols in parts:
                v=np.zeros_like(one)
                i=rows[0]
                for a,j in enumerate(cols):
                    q=polys[rows[1:],cols[:a]+cols[a+1:]]
                    v+=base[i,j]*q
                    coeff=B[:,i,j]
                    ix=np.flatnonzero(coeff.any(axis=1))
                    if len(ix):
                        products=mul(q[None,:short,:],coeff[ix,None,:],u,h)
                        for p,term in zip(ix,products):v[shift[p]]+=term
                polys[rows,cols]=v%mod
    F=polys[all4,all4]
    F[0,0]-=65
    return F

def det(A,u,h):
    n=A.shape[-2]
    t=np.zeros((*A.shape[:-3],2),dtype=np.int64);t[...,0]=1
    dp={0:t}
    for mask in range(1,1<<n):
        cols=[j for j in range(n) if mask>>j&1]
        r=len(cols)-1
        dp[mask]=sum(((-1)**(r+k))*mul(A[...,r,j,:],dp[mask^(1<<j)],u,h) for k,j in enumerate(cols))%mod
    return dp[(1<<n)-1]

def ring_eq(B,u,h):
    P=permanent_coeff(B,u,h)
    def projections(projs):
        return np.stack([B[:,:,i]@projs for i in range(2)],axis=-1)
    small=det(projections(F4)[:,minorrows,:,:],u,h).reshape(-1,2)
    full=det(projections(F6),u,h)
    family=full[len(six):].reshape(-1,3,2)
    assert ((family[:,1]-family[:,2])%2==0).all()
    mid=(family[:,1]-family[:,2])//2
    top=family[:,1]-family[:,0]-mid
    return np.concatenate((P,small,full[:len(six)],family[:,0],mid,top))%(mod//2)

def make(B,D,E,G,u,h):
    # pi^2=2u+2h*pi and pi^3=4hu+(2u+4h^2)*pi.
    return np.stack((B+2*u*E+4*h*u*G,D+2*h*E+(2*u+4*h*h)*G),axis=-1)%mod

def digit(B,D,E,G,k,u,h):
    vals=ring_eq(make(B,D,E,G,u,h),u,h)
    a,b=vals[:,0],vals[:,1]
    m=mod//2
    for _ in range(k):
        assert (a%2==0).all()
        m//=2
        ui=pow(u,-1,m)
        a,b=(b-h*a*ui)%m,(a//2*ui)%m
    return a%2
def fourth(flag,u,h,src):
    B,F,A,L,D,moves=model(flag)
    K=ker2(A)
    tag='-'.join(map(str,flag))
    rows=json.loads((src/(tag+'-third.json')).read_bytes())[h]
    outputs=[]
    zero=np.zeros_like(B)
    def direction(x):return (x@moves.reshape(60,96)).reshape(6,16)
    for row in rows:
        mask=row['mask']
        sel=np.array([(mask>>i)&1 for i in range(len(D))])
        V=direction(sel@K)
        def q(X):return ((equations(B+2*X)+equations(B-2*X)-2*F)//8)%2
        qv=q(V)
        M=np.array([L@(q(V+d)-qv-q(d))%2 for d in D]).T
        project=(ker2(M.T)@L)%2
        X=direction(np.array(row['e'])+np.array(row['t'])@K)
        dirs=[direction(v@K) for v in np.array(row['kernel'],dtype=np.int64)]
        def getG(x):
            c=digit(B,V,x,zero,3,u,h)
            g=linear(A,c)
            assert g is not None
            return direction(g)
        G=getG(X)
        GD=[getG(X+x)-G for x in dirs]
        def get(x,g):return project@digit(B,V,x,g,4,u,h)%2
        c=get(X,G)
        one=[get(X+x,G+g)-c for x,g in zip(dirs,GD)]
        pairs=list(combinations(range(len(dirs)),2))
        quad=[get(X+dirs[i]+dirs[j],G+GD[i]+GD[j])-c-one[i]-one[j] for i,j in pairs]
        polys=np.array([c,*one,*quad]).T%2
        keys=[0,*[1<<i for i in range(len(dirs))],*[(1<<i)|(1<<j) for i,j in pairs]]
        masks=np.arange(1<<len(dirs),dtype=np.uint32)
        for r in polys:
            if not len(masks):break
            y=np.zeros(len(masks),dtype=np.uint8)
            for k in np.flatnonzero(r):y^=(masks&keys[k])==keys[k]
            masks=masks[~y.astype(bool)]
        outputs.append((mask,masks.tolist()))
    print('flag',flag,'u,h',u,h,'survivors',sum(len(v) for _,v in outputs),flush=True)
    (src/(tag+'-fourth-'+str(u)+'-'+str(h)+'.json')).write_text(json.dumps(outputs))

    return sum(len(v) for _,v in outputs)

def verify(root):
    root.mkdir(exist_ok=True,parents=True)
    all_flags=list(flags())
    all_bases={basis(f)[0].tobytes() for f in all_flags}
    assert len(all_flags)==len(all_bases)==315
    seen=set()
    live=[]
    for flag in all_flags:
        B,_=basis(flag)
        if B.tobytes() in seen:continue
        O=orbit(B)
        assert O<=all_bases and not (O&seen)
        seen.update(O)
        dimension,_,count=jets(flag,root)
        print('flag',flag,'orbit size',len(O),'tangent dimension',dimension,'first digits',count,flush=True)
        if count:live.append((flag,len(O),count))
    assert seen==all_bases
    assert [(size,count) for _,size,count in live]==[(12,68),(6,32),(6,48),(12,128)]
    for flag,_,_ in live:
        third(flag,root)
        for u,h in [(1,0),(-1,0),(5,0),(-5,0),(-1,1),(-3,1)]:
            assert fourth(flag,u,h,root)==0
    print('No six-dimensional level space over any ramified quadratic extension of Q2.')

if __name__=='__main__':
    import argparse
    from tempfile import TemporaryDirectory
    ap=argparse.ArgumentParser()
    ap.add_argument('--work',type=Path)
    opt=ap.parse_args()
    if opt.work:verify(opt.work.resolve())
    else:
        with TemporaryDirectory() as d:verify(Path(d))
