"""Every complex symmetric 3-space on the permanent level has a star basis.

For the six upper off-diagonal coordinates e_ij on L, some vertex has its
three incident coordinates linearly independent. Relabel it as vertex 0:
then e_01,e_02,e_03 are coordinates on L. This reduces the full existence
question to the single 18-variable affine chart with pivots 01,02,03.

Proof. Write r_k(X) for the sum of all k-by-k subpermanents and r_0=1.
The coefficient of t^k in per(J+tX) is (4-k)! r_k(X). For a block diagonal
matrix the polynomial sum r_k t^k is the product for its blocks, by splitting
the partial matchings. Consequently every block has polynomial 1 when the
whole matrix does. In particular an isolated vertex has diagonal zero. On L
its diagonal functional thus belongs to the span of its three incident edge
functionals (a linear functional vanishing on their joint kernel). The six
edges together span the dual, since a diagonal level direction is zero.

Suppose no star is a basis. If triangle 012 forms a basis, name its edges
01=x,02=y,12=z. The remaining incident edges at vertex 0 and its diagonal
are combinations of x and y. Likewise at 1 and 2. At 3 the four incident
edge/diagonal functionals span at most two dimensions. This gives the first
system below. Any independent triangle can be relabeled 012.

If no triangle is a basis either, any three independent edges form a path
in K4. Relabel and normalize 01=x,12=y,23=z. The edge 02 lies in span(x,y)
by triangle 012 and in span(y,z) by star 2, hence is proportional to y.
The same holds for 13 using star 1 and triangle 123. If 02 or 13 is nonzero,
the star/triangle constraints at 0 and 3 put 03 in both spans, hence on y.
If both are zero, 03 is arbitrary. These are the other two systems.

All three finite-field calculations use deterministic F4 over F_31 and
test for the unit ideal over its algebraic closure. The union they cover
is closed: it consists of permanent-level Grassmannian points with all
four star determinants zero. Any complex solution gives a number-field
solution by the Nullstellensatz. At a place above 31 normalize at a rank-3
minor of least valuation; Cramer's rule makes the basis integral and rank
survives reduction. The closed conditions survive, after which the three
cases can be classified afresh. This argument does not require individual
affine charts to be proper.

Run: python SymmetricStarBasis.py --msolve /path/to/msolve
"""
from collections import defaultdict
from itertools import combinations,permutations
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from sympy import GF,Matrix,symbols
from sympy.polys.rings import ring

PAIRS=list(combinations(range(4),2))+[(i,i) for i in range(4)]
INDEX={q:k for k,q in enumerate(PAIRS)}
NAMES='a b c d e f g h i j k l'.split()

def equations(case):
    prime=31
    R,x,y,z,*coeffs=ring(' '.join(['x','y','z',*NAMES]),GF(prime))
    a,b,c,d,e,f,g,h,i,j,k,l=coeffs
    expr=[]
    if case=='triangle':
        off=[x,y,a*x+b*y,z,c*x+d*z,e*y+f*z]
        diag=[g*x+h*y,i*x+j*z,k*y+l*z]
        # Coefficient columns for edges 03,13,23 and diagonal 33.
        aa,bb,cc,dd,ee,ff,gg,hh,ii,jj,kk,ll=symbols(' '.join(NAMES))
        star=Matrix([[aa,cc,0,-2*(1+aa+cc)-gg-ii],
                     [bb,0,ee,-2*(1+bb+ee)-hh-kk],
                     [0,dd,ff,-2*(1+dd+ff)-jj-ll]])
        for cols in combinations(range(4),3):
            expr.append(str(star[:,list(cols)].det().expand()).replace('**','^').replace(' ',''))
    else:
        if case=='cut':
            off=[x,a*y,b*y,y,c*y,z]
        elif case=='cycle':
            off=[x,0,a*x+b*y+c*z,y,0,z]
        else:
            raise ValueError(case)
        diag=[d*x+g*y+j*z,e*x+h*y+k*z,f*x+i*y+l*z]
    matrix=[1+v for v in [*off,*diag,-2*sum(off)-sum(diag)]]
    F=R.zero-24
    for p in permutations(range(4)):
        term=R.one
        for i,j in enumerate(p):
            term*=matrix[INDEX[tuple(sorted((i,j)))]]
        F+=term
    groups=defaultdict(dict)
    for exp,coef in F.items():
        assert 2<=sum(exp[:3])<=4
        groups[exp[:3]][exp[3:]]=int(coef)
    for data in groups.values():
        terms=[]
        for ex,coef in data.items():
            factors=[s if k==1 else s+'^'+str(k) for s,k in zip(NAMES,ex) if k]
            if coef!=1 or not factors: factors.insert(0,str(coef))
            terms.append('*'.join(factors))
        expr.append('+'.join(terms))
    return ','.join(NAMES)+'\n31\n'+',\n'.join(expr)+'\n'

def verify(binary):
    with TemporaryDirectory() as tmp:
        folder=Path(tmp)
        def solve(name,data):
            path=folder/(name+'.in')
            out=path.with_suffix('.out')
            path.write_text(data,encoding='ascii')
            subprocess.run([binary,'-f',str(path),'-o',str(out),'-l','2','-t','1'],
                           check=True,capture_output=True)
            answer=out.read_text().strip()
            assert answer
            return answer
        assert solve('empty','x\n31\nx,x-1\n')=='[-1]:'
        assert solve('extension','x\n31\nx^2+1\n')!='[-1]:'
        for case in ('triangle','cut','cycle'):
            assert solve(case,equations(case))=='[-1]:',case
            print(case,'empty over the algebraic closure of F_31',flush=True)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--msolve',default='msolve')
    verify(parser.parse_args().msolve)
