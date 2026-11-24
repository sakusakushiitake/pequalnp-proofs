"""Every complex level space of 4-by-4 symmetric matrices invariant under
simultaneous cyclic permutation of rows and columns has dimension at most 2.
Run with Python 3 and SymPy. Arithmetic takes place in Q[z]/(z^4+1).
"""
from itertools import permutations
import sympy as s


def verify():
    z,t,u,v,a,b,c=s.symbols('z t u v a b c')
    cycl=z**4+1
    # Orbits of the 4-cycle on unordered pairs of indices, including the diagonal.
    orbits=[[(0,0),(1,1),(2,2),(3,3)],[(0,1),(1,2),(2,3),(0,3)],[(0,2),(1,3)]]
    def eigen(r,amps):
        vals=iter(amps)
        h=s.zeros(4)
        for orbit in orbits:
            if len(orbit)*r%4:
                continue
            x=next(vals)
            for j,(i,k) in enumerate(orbit):
                h[i,k]=h[k,i]=x*z**(2*j*r%8)
        return h
    def level(h):
        m=s.ones(4)+h
        f=sum(s.prod(m[i,j] for i,j in enumerate(p)) for p in permutations(range(4)))-24
        return s.rem(f,cycl,z).expand()
    # Any invariant subspace is the sum of its four eigenspaces.
    invariant=s.Poly(level(t*eigen(0,[a,b,c])),t)
    assert s.expand(invariant.nth(1)-24*(a+2*b+c))==0
    rest=[invariant.nth(i).subs(c,-a-2*b).expand() for i in (2,3,4)]
    assert list(s.groebner([h.subs(b,1) for h in rest],a,domain=s.QQ))==[1]
    assert any(h.subs({a:1,b:0})!=0 for h in rest)
    # Thus there is no nonzero fixed vector. The (-1)-eigenspace has a
    # nondegenerate quadratic constraint in dimension 3, so an isotropic
    # subspace in it has dimension at most 1.
    minus=s.Poly(level(t*eigen(2,[a,b,c])),t)
    q=minus.nth(2)
    assert s.det(s.hessian(q,(a,b,c)))!=0
    # In weight i the quartic leaves three projective directions. Its
    # conjugate gives the three directions in weight -i.
    imaginary=s.Poly(level(t*eigen(1,[a,b])),t)
    assert imaginary.as_dict().keys()=={(4,)}
    assert s.rem(imaginary.nth(4)-a**2*(-a+2*b*z)*(a+2*b*z),cycl,z).expand()==0
    # In particular each of these eigenspaces contributes at most one dimension.
    # Check every pair of candidate lines of opposite weight. No pair spans a
    # plane on the level set. z is a primitive eighth root, z^{-1}=-z^3.
    tested=0
    for x in (0,2*z,-2*z):
        for y in (0,-2*z**3,2*z**3):
            assert level(u*eigen(1,[x,1])+v*eigen(3,[y,1]))!=0
            tested+=1
    assert tested==9
    print("fixed directions: 0; opposite-character pairs on the level: 0/9; dimension <= 2")


if __name__=='__main__':
    verify()
