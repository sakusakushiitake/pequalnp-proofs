"""Exact order-three and Klein-four tests for the complex symmetric permanent level.

Together with the independent order-four test in SymmetricCyclicFour.py,
these computations bound the stabilizer of any prospective 3-space by 2.
The group acts by the same permutation on rows and columns.
"""
from itertools import permutations,product
import sympy as s


def character_basis(perms,factors):
    cells={(i,j) for i in range(4) for j in range(i,4)}
    mats=[]
    while cells:
        root=min(cells)
        orbit={root:0}
        queue=[root]
        good=True
        while queue:
            i,j=queue.pop()
            for perm,weight,order in zip(perms,*factors):
                k=tuple(sorted((perm[i],perm[j])))
                degree=(orbit[i,j]+weight)%order
                if k not in orbit:
                    orbit[k]=degree
                    queue.append(k)
                elif orbit[k]!=degree:
                    good=False
        cells-=set(orbit)
        if good:
            mats.append(orbit)
    return mats


def level(orb,unit,t):
    a=s.symbols('a:'+str(len(orb)))
    matrix=s.ones(4)
    for coeff,v in zip(a,orb):
        for (i,j),k in v.items():
            matrix[i,j]=matrix[j,i]=1+t*coeff*unit**k
    poly=sum(s.prod(matrix[i,j] for i,j in enumerate(p)) for p in permutations(range(4)))-24
    return a,poly.expand()


def excludes_projective(eqs,coords,extra=(),rel=()):
    for i,x in enumerate(coords):
        use={a:0 for a in coords[:i]}
        use[x]=1
        rows=[f.subs(use).expand() for f in eqs]+list(rel)
        var=tuple(coords[i+1:])+tuple(extra)
        if var:
            assert list(s.groebner(rows,*var,domain=s.QQ))==[1]
        else:
            assert any(v!=0 for v in rows)


def verify():
    t,z=s.symbols('t z')
    cyc=[(1,2,0,3)]
    a,f=level(character_basis(cyc,([0],[3])),1,t)
    p=s.Poly(f,t)
    last=s.solve(p.nth(1),a[-1])[0]
    excludes_projective([p.nth(k).subs(a[-1],last) for k in (2,3,4)],a[:-1])
    # The two nontrivial characters are conjugate. The ternary cubic for
    # either one is smooth: its three partials have no common projective zero.
    # A smooth complex plane cubic contains no line, by Bezout's theorem.
    a,f=level(character_basis(cyc,([1],[3])),z,t)
    p=s.Poly(s.rem(f,z*z+z+1,z),t)
    assert p.as_dict().keys()=={(3,)} and len(a)==3
    excludes_projective([p.nth(3).diff(x) for x in a],a,(z,),(z*z+z+1,))
    print("cyclic order 3: fixed dimension 0, each other character dimension <= 1")
    # Representatives of the two S4-conjugacy classes of Klein-four groups.
    for gens,expected in [([(1,0,3,2),(2,3,0,1)],1), ([(1,0,2,3),(0,1,3,2)],2)]:
        for weights in product(range(2),repeat=2):
            a,f=level(character_basis(gens,(weights,[2,2])),-1,t)
            p=s.Poly(f,t)
            if weights==(0,0):
                last=s.solve(p.nth(1),a[-1])[0]
                hess=s.hessian(p.nth(2).subs(a[-1],last),a[:-1])
                assert hess.rank()==len(a)-1 and hess.rank()//2==expected
            else:
                excludes_projective([coef for _,coef in p.terms()],a)
        print("Klein four",gens,"dimension <=",expected)


if __name__=='__main__':
    verify()
