"""Six-dimensional permanent-level spaces at I+J and cubic number fields.

Recheck the totally ramified cubic completion at 2 using Python and NumPy.
The earlier unramified calculation, nilpotent-space classification and the
proof that every reduction comes from a complete flag are explained at
https://github.com/sakusakushiitake/pequalnp-proofs/blob/872578d2c53cd41df1d526607b0455325ba4e1bc/research/PermanentUnramified.py .
The Hall-minor equations used here are derived at
https://github.com/sakusakushiitake/pequalnp-proofs/blob/4db0501c6388724b5b7b4b9f1023db0cb5458722/research/PermanentQuadraticFields.py .

At a place above 2, a cubic number field either has an unramified place
or has exactly one totally ramified place of degree three. In the latter
case the local extension is tame, with residue field F2. For any uniformizer
t, the unit 2/t^3 has a cube root by Hensel's lemma with residue 1 and odd
derivative. A new uniformizer pi satisfies pi^3=2.

Let B represent the special-fibre flag in a Grassmann chart, F the integral
permanent and projection-minor coefficient vector, A its derivative mod 2,
K a basis for ker A, L a basis for the left kernel. Expand the chart at
B+pi*D+pi^2*E+pi^3*G+pi^4*H+pi^5*I+pi^6*J. At each order a new digit
appears only via A. A residual is solvable precisely when its image under L
vanishes. Thus arbitrary higher digits can be treated by linear algebra.

Orders 1-3: enumerate binary D in K. Its second-order obstruction is
quadratic; after choosing a linear right inverse for A, its third-order
obstruction has Boolean degree at most three in D and is affine in the
kernel coordinates of E. Evaluate all degree-at-most-three coefficients by
Boolean interpolation and solve each affine system. All 315 binary flags
are covered by seventeen orbits under simultaneous permutation and transpose.

Order 4: on each surviving affine family E(z), G has a particular solution
affine in z. Its free directions act linearly on the fourth-order residual,
which is quadratic in z after projecting away these directions and A H.
The symmetric integer differences in the code extract the needed Hasse
coefficients modulo two. At orders 5 and 6 use independent direct polynomial
evaluation in the cubic ring, with triples a+b*pi+c*pi^2. The kth binary
digit of an expression known to vanish to order k is obtained from component
(k mod 3), shifted by floor(k/3) binary places.

Order 5: for each surviving (D,E) the order-four projection annihilates
every free G direction. The code checks solvability for the zero and basis
choices. H is chosen by linear correction; shifting H by K has no projected
effect at order five, as checked for each surviving D (the coefficient is
the mixed Hessian in D and the shift). The remaining order-five residual
is affine in the free G coordinates, as G enters first at order three.
The eight surviving pairs all have D=0.

Order 6: now H at order four is independent of G. Enumerate every surviving
G; choose I to cancel the order-five residual. Its free kernel part can
first affect a later order since D=0. At order six the free H acts by the
polarized quadratic Hasse coefficient in (E,H), independent of G. Solve
for H and the new digit J. All corrections are in the chart's sixty free
coordinates, so the identity pivot minor is preserved.

The ordinary integer computations before the ring stage use signed
64-bit arithmetic; each input magnitude and the crude Leibniz determinant
bound are checked. Ring arithmetic afterwards reduces intermediate products
modulo 512. This exceeds the precision needed even after the exact division
by two in the pencil equations. The flag-space argument and these local
calculations do not settle the complex existence question.
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


from itertools import permutations,product
from time import monotonic
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
    m=int(np.abs(B).max())
    assert 2*720*(2*max(1,m))**6 < 2**63 and 24*(2+6*m)**4 < 2**63
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

def pack(x):return int.from_bytes(np.packbits(np.asarray(x,dtype=np.uint8)%2,bitorder='little').tobytes(),'little')
def restrict_inverse(A):
    _,p=reduce2(A)
    _,rows=reduce2(A[:,p].T)
    r=len(p)
    M,pc=reduce2(np.column_stack((A[rows][:,p],np.eye(r,dtype=np.uint8))))
    assert pc==list(range(r))
    J=np.zeros((A.shape[1],len(rows)),dtype=np.int64)
    J[p]=M[:,r:]
    return J,rows

def solve_bits(cols,b):
    rows={};ker=[]
    for j,x in enumerate(cols):
        s=1<<j
        while x and x.bit_length() in rows:
            a,z=rows[x.bit_length()];x^=a;s^=z
        if x:rows[x.bit_length()]=(x,s)
        else:ker.append(s)
    s=0
    while b:
        p=b.bit_length()
        if p not in rows:return None
        a,z=rows[p];b^=a;s^=z
    return s,ker

def third(flag,root):
    B,F,A,L,D,moves=model(flag);K=ker2(A);d=len(D)
    J,rows=restrict_inverse(A)
    small=np.array([equations(B+2*e) for e in moves])
    H=[]
    for v in D:
        f=equations(B+2*v)
        vals=np.array([equations(B+2*(v+e)) for e in moves])-f-small+F
        assert (vals%4==0).all()
        H.append(((vals//4)%2@L.T)%2)
    H=np.array(H)
    HK=[[pack(y) for y in K@v%2] for v in H]
    size=1<<d
    samples=[(0,0)]*size
    for k in range(4):
        for I in combinations(range(d),k):
            v=D[list(I)].sum(axis=0,dtype=np.int64) if I else np.zeros_like(B)
            p2,m2,p4,m4=[equations(B+t*v) for t in (2,-2,4,-4)]
            q=(p2+m2-2*F)//8
            third=((p2-m2)//4-(p4-m4)//8)//4
            e=J@q[rows]%2
            h=sum((H[i] for i in I),np.zeros_like(H[0]))%2
            v0=pack(L@q)
            v1=pack(L@(third+F//2)+e@h)
            mask=sum(1<<i for i in I)
            sub=(mask-1)&mask
            while mask:
                a,b=samples[sub];v0^=a;v1^=b
                if not sub:break
                sub=(sub-1)&mask
            samples[mask]=(v0,v1)
    # The two obstruction polynomials have Boolean degree at most two and three.
    for i in range(d):
        for m in range(size):
            if (m>>i)&1:
                a,b=samples[m^(1<<i)]
                c,e=samples[m];samples[m]=(a^c,b^e)
    res=[]
    eligible=0
    for m,(v0,v1) in enumerate(samples):
        if v0:continue
        eligible+=1
        cols=[0]*d
        for i in range(d):
            if m>>i&1:cols=[a^b for a,b in zip(cols,HK[i])]
        sol=solve_bits(cols,v1)
        if sol:res.append((m,*sol))
    print(flag,'first digits surviving the cone',eligible,'third order',len(res),'second digits',sum(1<<len(t[2]) for t in res),flush=True)
    (root/('-'.join(map(str,flag))+'.json')).write_text(json.dumps(res))

    return len(res)
def digits(m,n):return np.array([(m>>i)&1 for i in range(n)],dtype=np.int64)

def fourth(root):
    f=(7,1,2,8)
    B,F,A,L,D,moves=model(f);K=ker2(A);d=len(K)
    J,piv=restrict_inverse(A)
    def direction(x):return (x@moves.reshape(60,96)).reshape(6,16)
    small=[equations(B+2*v) for v in moves]
    H=[]
    for v in D:
        ff=equations(B+2*v)
        H.append(np.array([(equations(B+2*(v+e))-ff-s+F)//4%2 for e,s in zip(moves,small)]))
    H=np.array(H)
    rows=json.loads((root/'7-1-2-8.json').read_bytes())
    results=[]
    for count,(mask,offset,ker) in enumerate(rows):
        bits=digits(mask,d)
        V=direction(bits@K)
        hm=H[bits.astype(bool)].sum(axis=0,dtype=np.int64)%2
        p2,m2,p4,m4=[equations(B+t*V) for t in (2,-2,4,-4)]
        q2=(p2+m2-2*F)//8
        q4=((p4+m4-2*F)//32-q2)//12
        v1=(p4-m4)//8
        assert (v1%2==0).all()
        q3=((p2-m2)//4-v1)//4
        e=J@q2[piv]%2
        assert ((A@e-q2)%2==0).all()
        z0=e+digits(offset,d)@K
        S=np.array([digits(t,d) for t in ker],dtype=np.int64).reshape(-1,d)
        basis=S@K
        Proj=(ker2((L@hm.T@K.T%2).T)@L)%2
        def residual(y):
            E=direction(y)
            target=(F//2+q3+y@hm)%2
            g=(J@target[piv])%2
            assert ((A@g-target)%2==0).all()
            f0=equations(B+2*E)
            qe=(f0+equations(B-2*E)-2*F)//8
            changed=(equations(B+2*E+2*V)+equations(B+2*E-2*V)-2*f0)//8
            assert ((changed-q2)%2==0).all()
            return Proj@(v1//2+q4+g@hm+qe+(changed-q2)//2)%2
        c=residual(z0)
        coeff=[c]+[residual(z0+v)-c for v in basis]
        pairs=list(combinations(range(len(basis)),2))
        for i,j in pairs:
            hx=H[S[i].astype(bool)].sum(axis=0,dtype=np.int64)
            coeff.append(Proj@(basis[j]@hx)%2)
        rr=np.array(coeff).T%2
        keys=[0,*[1<<i for i in range(len(basis))],*[(1<<i)|(1<<j) for i,j in pairs]]
        masks=np.arange(1<<len(basis),dtype=np.uint32)
        for r in rr:
            if not len(masks):break
            val=np.zeros(len(masks),dtype=np.uint8)
            for k in np.flatnonzero(r):val^=(masks&keys[k])==keys[k]
            masks=masks[~val.astype(bool)]
        if len(masks):results.append((mask,masks.tolist()))
        if count%12==0:print('first digit',count,'of',len(rows),'surviving pairs',sum(len(v) for _,v in results),flush=True)
    print('cubic fourth jet',len(results),'first digits',sum(len(v) for _,v in results),'second digits',flush=True)
    (root/'fourth.json').write_text(json.dumps(results))

mod=512
def mul(x,y):
    a,b,c=x[...,0],x[...,1],x[...,2]
    d,e,f=y[...,0],y[...,1],y[...,2]
    return np.stack(((a*d+2*(b*f+c*e))%mod,(a*e+b*d+2*c*f)%mod,(a*f+b*e+c*d)%mod),axis=-1)

def permanent_coeff(B):
    B=B.reshape(6,4,4,3)
    one=np.zeros((len(mons),3),dtype=np.int64)
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
                        products=mul(q[None,:short,:],coeff[ix,None,:])
                        for p,term in zip(ix,products):v[shift[p]]+=term
                polys[rows,cols]=v%mod
    F=polys[all4,all4]
    F[0,0]-=65
    return F

def det(A):
    n=A.shape[-2]
    t=np.zeros((*A.shape[:-3],3),dtype=np.int64);t[...,0]=1
    dp={0:t}
    for mask in range(1,1<<n):
        cols=[j for j in range(n) if mask>>j&1]
        r=len(cols)-1
        dp[mask]=sum(((-1)**(r+k))*mul(A[...,r,j,:],dp[mask^(1<<j)]) for k,j in enumerate(cols))%mod
    return dp[(1<<n)-1]

def ring_eq(B):
    P=permanent_coeff(B)
    def projections(projs):
        return np.stack([B[:,:,i]@projs for i in range(3)],axis=-1)
    small=det(projections(F4)[:,minorrows,:,:]).reshape(-1,3)
    full=det(projections(F6))
    family=full[len(six):].reshape(-1,3,3)
    assert ((family[:,1]-family[:,2])%2==0).all()
    mid=(family[:,1]-family[:,2])//2
    top=family[:,1]-family[:,0]-mid
    return np.concatenate((P,small,full[:len(six)],family[:,0],mid,top))%(mod//2)

def fifth(root):
    flag=(7,1,2,8)
    B,F,A,L,_,moves=model(flag);K=ker2(A);d=len(K)
    J,piv=restrict_inverse(A)
    rows={mask:(offset,ker) for mask,offset,ker in json.loads((root/'7-1-2-8.json').read_bytes())}
    fourth=json.loads((root/'fourth.json').read_bytes())
    def direction(x):return (x@moves.reshape(60,96)).reshape(6,16)
    def solve(rhs):
        x=J@rhs[piv]%2
        assert ((A@x-rhs)%2==0).all()
        return x
    def values(D,E,G=0,H=0):
        return ring_eq(np.stack((B+2*G,D+2*H,E),axis=-1))
    def digit(R,k):
        for i in range(k):
            assert ((R[:,i%3]//(2**(i//3)))%2==0).all()
        return R[:,k%3]//(2**(k//3))%2
    def extends(const,cols):
        if not len(cols):return not const.any()
        return not (ker2(np.array(cols))@const%2).any()
    zero=np.zeros_like(B)
    start=monotonic()
    results=[]
    for mask,choices in fourth:
        D=direction(digits(mask,d)@K)
        e0=solve(digit(values(D,zero),2))
        offset,ker=rows[mask]
        for index,m in enumerate(choices):
            v=offset
            for j,weight in enumerate(ker):
                if m>>j&1:v^=weight
            E=direction(e0+digits(v,d)@K)
            G=direction(solve(digit(values(D,E),3)))
            def res(g):
                H=direction(solve(digit(values(D,E,g),4)))
                return L@digit(values(D,E,g,H),5)%2
            c=res(G)
            if index==0:
                H=direction(solve(digit(values(D,E,G),4)))
                for row in K:
                    assert ((L@digit(values(D,E,G,H+direction(row)),5)-c)%2==0).all()
            cols=[(res(G+direction(row))-c)%2 for row in K]
            if extends(c,cols):results.append((mask,m))
            if index%16==0:print('order five',mask,index,len(choices),'survivors',len(results),'seconds',round(monotonic()-start),flush=True)
    (root/'fifth.json').write_text(json.dumps(results))
    print('pairs extending through order five',len(results),flush=True)
def sixth(root):
    B,F,A,L,_,moves=model((7,1,2,8))
    K=ker2(A);d=len(K);J,piv=restrict_inverse(A)
    rows={mask:(offset,ker) for mask,offset,ker in json.loads((root/'7-1-2-8.json').read_bytes())}
    fifth=json.loads((root/'fifth.json').read_bytes())
    def direction(x):return (x@moves.reshape(60,96)).reshape(6,16)
    def solve(rhs):
        x=J@rhs[piv]%2
        assert ((A@x-rhs)%2==0).all()
        return x
    zero=np.zeros_like(B)
    def values(E,G=zero,H=zero,I=zero):
        return ring_eq(np.stack((B+2*G,2*H,E+2*I),axis=-1))
    def digit(R,k):
        for i in range(k):
            assert ((R[:,i%3]//(2**(i//3)))%2==0).all()
        return R[:,k%3]//(2**(k//3))%2
    def solve_affine(f):
        c=f(zero)
        return solve_bits([pack((f(direction(t))-c)%2) for t in K],pack(c))
    def expand(pair):
        off,basis=pair
        for bits in product((0,1),repeat=len(basis)):
            mask=off
            for b,t in zip(bits,basis):
                if b: mask^=t
            yield mask
    results=[]
    for first,m in fifth:
        assert first==0
        v,ker=rows[0]
        for j,t in enumerate(ker):
            if m>>j&1:v^=t
        E=direction(digits(v,d)@K)
        G0=direction(solve(digit(values(E),3)))
        H0=direction(solve(digit(values(E,G0),4)))
        gg=solve_affine(lambda g:L@digit(values(E,G0+g,H0),5)%2)
        assert gg
        cols=None
        for gm in expand(gg):
            G=G0+direction(digits(gm,d)@K)
            I=direction(solve(digit(values(E,G,H0),5)))
            c=L@digit(values(E,G,H0,I),6)%2
            if cols is None:
                cols=[pack((L@digit(values(E,G,H0+direction(t),I),6)-c)%2) for t in K]
            hh=solve_bits(cols,pack(c))
            if hh:results.append((m,gm,hh))
        print('second digit',m,'third digits',1<<len(gg[1]),'surviving triples cumulative',len(results),flush=True)
    (root/'sixth.json').write_text(json.dumps(results))
    print('triples surviving order six',len(results),flush=True)


def verify(root):
    root.mkdir(exist_ok=True,parents=True)
    all_flags=list(flags())
    all_bases={basis(f)[0].tobytes() for f in all_flags}
    assert len(all_bases)==len(all_flags)==315
    seen=set();live=[];count=0
    for f in all_flags:
        B,_=basis(f)
        if B.tobytes() in seen: continue
        orbit_f=orbit(B)
        assert orbit_f<=all_bases and not orbit_f.intersection(seen)
        seen.update(orbit_f);count+=1
        if third(f,root):live.append(f)
    assert seen==all_bases and count==17 and live==[(7,1,2,8)]
    fourth(root)
    four=json.loads((root/'fourth.json').read_bytes())
    assert len(four)==4 and sum(len(v) for _,v in four)==320
    fifth(root)
    five=json.loads((root/'fifth.json').read_bytes())
    assert len(five)==8 and all(d==0 for d,e in five)
    sixth(root)
    assert json.loads((root/'sixth.json').read_bytes())==[]
    print('No six-dimensional permanent-level space over any cubic number field.',flush=True)

if __name__=='__main__':
    import argparse
    from tempfile import TemporaryDirectory
    ap=argparse.ArgumentParser()
    ap.add_argument('--work',type=Path)
    args=ap.parse_args()
    if args.work:verify(args.work.resolve())
    else:
        with TemporaryDirectory() as tmp:verify(Path(tmp))
