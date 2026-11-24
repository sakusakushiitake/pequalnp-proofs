"""No six-dimensional permanent level at J+I over any unramified 2-adic field.

For A=I+J of order four, per(A)=65 and det(A)=5. Over the complex numbers
any constant-level space through A has dimension at most six. Indeed the
relevant closed scheme in the Grassmannian is defined over Z. A complex
point yields an algebraic point; choosing an integral Grassmann chart at a
prime above two preserves dimension. Since per=det in characteristic two,
the reduced directions multiplied on the left by A^{-1} form a space of
nilpotents: det(I+tX)=1 identically. Gerstenhaber's dimension bound and
equality classification give the bound six and, at equality, exactly the
strictly upper triangular space in a suitable basis. This theorem holds
over arbitrary fields; see https://arxiv.org/abs/1210.4951 .

For a prospective six-space over a finite extension of Q_2 with
ramification index one, the following verifies that it cannot lift modulo 8.
Permuting coordinates puts its residue flag in the lower unitriangular
chart U; simultaneous index permutations preserve A and the level.
Write T for the matrix of six independent strictly upper entries. Lift U
to the integers of the local field. The baseline A U(I+T)U^{-1} has
constant determinant five. Therefore its permanent error divided by two is
the sum of the twelve odd permutation products minus 30. Modulo two it is
a polynomial in T and the six flag coordinates. Arbitrary first corrections
inside U coordinates are 2 M(T) with M any matrix of linear forms. Modulo
four they contribute tr((I+T)^{-1}M(T)) to the divided error; det(A)=1 in
the residue field. Eliminating this constant rank-38 image leaves 75 flag
equations. A deterministic Groebner basis over F_2 forces the flag point to
have (u0,u1,u2,u4,u5)=(1,1,0,0,0) and u3^2=u3, even over the algebraic
closure. Thus every surviving residue flag is binary.

The 315 binary flags give 12 surviving flags, all in one orbit under
simultaneous index permutations and transpose. In the fixed Grassmann chart
for one representative, write the modulo-four solutions as C+sum(s_i D_i)
with 22 first correction digits. All polynomial coefficients of the error
are divisible by four in this parametrization. Divide by four and project
away the new linear correction for modulo eight. The resulting equations
have degree at most two modulo two. One equation is the constant one,
even without imposing the binary field equations on the digits. This
excludes all finite unramified extensions of Q_2, including Q_2 itself.
It leaves the ramified case and complex existence open.

Use Python 3, NumPy and msolve. Run with --msolve PATH, or generate the
input with --generate DIR and independently run the basis check with
--check DIR --msolve PATH. No workspace-specific files are needed.
"""
def verify(root,binary):
    import subprocess
    from tempfile import TemporaryDirectory
    with TemporaryDirectory() as d:
        out=Path(d)/'basis.out'
        subprocess.run([binary,'-f',str(root/'flags.in'),'-o',str(out),'-g','2','-l','2','-t','1'],check=True)
        basis_text=out.read_text()
        assert '#field characteristic: 2' in basis_text and '#length of basis:      9' in basis_text
        polys={line.strip('[], :') for line in basis_text.splitlines() if not line.startswith('#')}
        assert {'1*u4^1','1*u2^1','1*u5^2','1*u3^2+1*u3^1','1*u1^2+1','1*u0^2+1'}<=polys
    print('Every residue flag lifting modulo four is binary in the normalized chart.')


from pathlib import Path
import sys
if __name__=='__main__' and '--check' in sys.argv:
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',required=True,type=Path)
    parser.add_argument('--msolve',default='msolve')
    args=parser.parse_args()
    verify(args.check.resolve(),args.msolve)
    raise SystemExit(0)
from collections import Counter
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json
import numpy as np

w=Path(__file__).resolve().parent
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

def binary_system(columns,target):
    E={}
    def reduce(v):
        while v:
            h=v.bit_length()-1
            if h not in E:break
            v^=E[h]
        return v
    def pack(v):
        return int.from_bytes(np.packbits(v%2,bitorder='little').tobytes(),'little')
    for c in columns:
        v=reduce(pack(c))
        if v:E[v.bit_length()-1]=v
    return len(E),reduce(pack(target))==0

def audit(flag):
    B,p=basis(flag)
    assert len(p)==6
    F,cofs=coeffs(B)
    assert F[0]==0 and (F%2==0).all()
    cols=[]
    for j in range(16):
        if j in p: continue
        for k in range(6):
            c=np.zeros(len(mons),dtype=np.uint8)
            c[shift[k]]=cofs[j][:short]%2
            cols.append(c)
    assert len(cols)==60
    rank,lift=binary_system(cols,F//2)
    return dict(flag=flag,rank=rank,lift=lift)

def binary_flags():
    records=[audit(f) for f in flags()]
    assert len(records)==315 and len({basis(r['flag'])[0].tobytes() for r in records})==315
    print(Counter((r['rank'],r['lift']) for r in records),flush=True)
    return records


from itertools import permutations
one={0}
zero=set()
def add(*xs):
    out=set()
    for x in xs:out.symmetric_difference_update(x)
    return out
def times(a,b):
    if len(a)>len(b):a,b=b,a
    out=set()
    for x in a:out.symmetric_difference_update(x+y for y in b)
    return out
def matmul(a,b):
    return [[add(*[times(a[i][k],b[k][j]) for k in range(4)]) for j in range(4)] for i in range(4)]
def identity():
    return [[one if i==j else zero for j in range(4)] for i in range(4)]
def mplus(*xs):
    return [[add(*[x[i][j] for x in xs]) for j in range(4)] for i in range(4)]

def universal(project=True):
    T=[[set() for _ in range(4)] for _ in range(4)]
    N=[[set() for _ in range(4)] for _ in range(4)]
    for h,(i,j) in enumerate(combinations(range(4),2)):
        T[i][j]={1<<(4*h)}
        N[j][i]={1<<(24+4*h)}
    I=identity()
    T2=matmul(T,T)
    W=mplus(I,T,T2,matmul(T2,T))
    N2=matmul(N,N)
    U=mplus(I,N)
    V=mplus(I,N,N2,matmul(N2,N))
    assert matmul(U,V)==I
    A=[[one if base[i,j]%2 else zero for j in range(4)] for i in range(4)]
    Y=matmul(A,matmul(U,matmul(mplus(I,T),V)))
    odd=set()
    for p in permutations(range(4)):
        if sum(p[i]>p[j] for i,j in combinations(range(4),2))%2:
            odd=add(odd,times(times(Y[0][p[0]],Y[1][p[1]]),times(Y[2][p[2]],Y[3][p[3]])))
    mask=(1<<24)-1
    ts=[sum(1<<(4*j) for j in m) for m in mons]
    idx={t:i for i,t in enumerate(ts)}
    F=[set() for _ in ts]
    for key in odd:F[idx[key&mask]].add(key>>24)
    cols=[]
    for i in range(4):
        for j in range(4):
            for k in range(6):
                col=np.zeros(len(ts),dtype=np.uint8)
                for t in W[j][i]:col[idx[t+(1<<(4*k))]]=1
                cols.append(col)
    reduced,piv=reduce2(cols)
    assert len(piv)==38
    for i,p in enumerate(piv):
        for j in np.flatnonzero(reduced[i]):
            if j!=p:F[j]=add(F[j],F[p])
        F[p]=set()
    return [s for s in F if s] if project else (F,reduced,piv,W)

def pretty(a):
    parts=[]
    for j in range(6):
        e=(a>>(4*j))&15
        if e:parts.append('u'+str(j)+('^'+str(e) if e>1 else ''))
    return '*'.join(parts) or '1'

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

def octic(flag):
    B,p=basis(flag)
    F,cofs=coeffs(B)
    moves=[]
    cols=[]
    for j in range(16):
        if j in p: continue
        for k in range(6):
            v=np.zeros((6,16),dtype=np.int64)
            v[k,j]=1
            moves.append(v.ravel())
            c=np.zeros(len(mons),dtype=np.int64)
            c[shift[k]]=cofs[j][:short]%2
            cols.append(c)
    A=np.asarray(cols).T
    t=(F//2)%2
    R,pv=reduce2(np.column_stack((A,t)))
    assert len(pv)==38 and 60 not in pv
    point=np.zeros(60,dtype=np.int64)
    point[pv]=R[:len(pv),-1]
    assert np.array_equal(A@point%2,t)
    K=ker2(A)
    left=ker2(A.T)
    moves=np.array(moves)
    C=B+2*(point@moves).reshape(6,16)
    D=2*(K@moves).reshape(-1,6,16)
    def val(U):
        raw=coeffs(U)[0]
        assert (raw%4==0).all()
        return left@(raw//4)
    q0=val(C)
    coeff=[q0]
    names=['u'+str(i) for i in range(len(D))]
    mon=['1']
    unit=[]
    for i,V in enumerate(D):
        e=val(C+V)-q0
        d=val(C+2*V)-q0
        assert (d%2==0).all()
        unit.append(e)
        coeff.extend((d//2,e-d//2))
        mon.extend((names[i],names[i]+'^2'))
    for i,j in combinations(range(len(D)),2):
        coeff.append(val(C+D[i]+D[j])-q0-unit[i]-unit[j])
        mon.append(names[i]+'*'+names[j])
    coeff=np.array(coeff).T%2
    ex=[]
    for row in coeff:
        terms=[m for m,r in zip(mon,row) if r]
        if terms:ex.append('+'.join(terms))
    assert "1" in ex and len(ex)==47
    return ex.count("1")

def generate(root):
    root.mkdir(exist_ok=True,parents=True)
    F=universal()
    names=['u'+str(i) for i in range(6)]
    assert len(F)==75
    eqs=['+'.join(pretty(m) for m in sorted(s)) for s in F]
    (root/'flags.in').write_text(','.join(names)+'\n2\n'+',\n'.join(eqs)+'\n',newline='\n')
    entries=binary_flags()
    assert Counter((r['rank'],r['lift']) for r in entries)=={(38,False):303,(38,True):12}
    allowed=[r['flag'] for r in entries if r['lift']]
    B,_=basis(allowed[0])
    assert orbit(B)=={basis(f)[0].tobytes() for f in allowed}
    constants=octic(allowed[0])
    print('Twelve flags in one orbit; number of constant-one modulo-eight equations:',constants)

if __name__=='__main__':
    import argparse
    from tempfile import TemporaryDirectory
    ap=argparse.ArgumentParser()
    mode=ap.add_mutually_exclusive_group()
    mode.add_argument('--generate',type=Path)
    mode.add_argument('--check',type=Path)
    ap.add_argument('--msolve',default='msolve')
    args=ap.parse_args()
    if args.generate:generate(args.generate.resolve())
    elif args.check:verify(args.check.resolve(),args.msolve)
    else:
        with TemporaryDirectory() as d:
            generate(Path(d))
            verify(Path(d),args.msolve)
