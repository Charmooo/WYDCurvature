"""Cleared numerators as exponential polynomials: coefficients in Z[d], exponents (i1+j1 d)u+(i2+j2 d)v."""
import sys
from flint import fmpz_mpoly_ctx, Ordering, fmpz
from collections import defaultdict
# ring: d, and Laurent exponentials handled as dict {(i1,j1,i2,j2): fmpz_poly in d}
from flint import fmpz_poly
def P(*c): return fmpz_poly(list(c))
class EP:
    __slots__=('t',)
    def __init__(s,t): s.t={k:c for k,c in t.items() if c!=0}
    def __add__(s,o):
        r=dict(s.t)
        for k,c in o.t.items(): r[k]=r.get(k,0)+c
        return EP(r)
    def __sub__(s,o): return s+o.sc(-1)
    def sc(s,c): return EP({k:x*c for k,x in s.t.items()})
    def __mul__(s,o):
        r={}
        for k,c in s.t.items():
            for l,e in o.t.items():
                m=(k[0]+l[0],k[1]+l[1],k[2]+l[2],k[3]+l[3]); z=r.get(m); r[m]=c*e if z is None else z+c*e
        return EP(r)
    def sq(s): return s*s
def one(c=1): return EP({(0,0,0,0):P(c)})
def ex(i,j,g):  # e^{(i+jd) * gap}, gap (cu,cv)
    return (i*g[0],j*g[0],i*g[1],j*g[1])
d=P(0,1)
def fphi(g,k):
    """k-th derivative (wrt own argument) of 2 f, f= sinh(d s) - d sinh s"""
    t=defaultdict(lambda:P(0))
    s=(-1)**(k+1)
    t[ex(0,1,g)]+=d**k; t[ex(0,-1,g)]+=s*d**k; t[ex(1,0,g)]+=-d; t[ex(-1,0,g)]+=-s*d
    return EP(t)
def nums():
    gp={(1,0):(1,0),(2,1):(0,1),(2,0):(1,1)}
    ph={}
    for (b,a),g in gp.items():
        ph[(b,a)]=[fphi(g,k) for k in range(4)]; ph[(a,b)]=[fphi((-g[0],-g[1]),k) for k in range(4)]
    # pos of sigma_c-sigma_k
    xw=[EP({ex(1,0,(1,1)):P(1)}),EP({ex(1,0,(0,1)):P(1)}),one()]
    def jp(i,j,e,k=0,o=2):
        de=e[i]-e[j] if isinstance(e[i],int) else None
        if de is None:
            dd=e[i]-e[j]; return [ph[(i,j)][k],dd*ph[(i,j)][k+1]]
        return [ph[(i,j)][k],ph[(i,j)][k+1].sc(de)]+([ph[(i,j)][k+2].sc(de*de)] if o==2 else [])
    def jm(a,b):
        r=[a[0]*b[0],a[0]*b[1]+a[1]*b[0]]
        if len(a)>2 and len(b)>2: r.append(a[0]*b[2]+(a[1]*b[1]).sc(2)+a[2]*b[0])
        return r
    sub=lambda f,g:[s-t for s,t in zip(f,g)]
    add=lambda f,g:[s+t for s,t in zip(f,g)]
    # phi = f/(d(D-1)), each ph is 2f. T = N^2/(16 p p p): in f: T = (d(D-1)) * Nf^2/(16 pf^3) ; with 2f: T = 2 d(D-1) N2^2/(16 p2 p2 p2)
    fac=2*d*(d*d-1)
    out={}
    for i in range(3):
        j,k=[t for t in range(3) if t!=i]; e=[0,0,0]; e[i]=1
        x=[[xw[t],xw[t].sc(-e[t]),xw[t].sc(e[t])] for t in range(3)]
        Nn=None
        for (a,b),c in (((0,1),2),((1,2),0),((2,0),1)):
            q=jm(x[c],jp(a,b,e)); Nn=q if Nn is None else add(Nn,q)
        pij,pik,pjk=jp(i,j,e,1),jp(i,k,e,1),jp(j,k,e,1)
        Pp=jm(pij,pik)
        def quot(A,Q):
            A0,A1,A2=A;P0,P1,P2=Q
            f2=(A2*P0-(A1*P1).sc(2)-A0*P2)*P0+(A0*P1*P1).sc(2)
            return f2-((A1*P0-A0*P1)*P0).sc(2)
        T=quot(jm(Nn,Nn),Pp).sc(3*fac)
        X=[jm(t,t) for t in x]; km=lambda b,a: sub(jp(b,a,e),jp(b,a,e,1))
        V=pjk[0]*quot(jm(X[i],jm(km(j,i),km(k,i))),Pp)+pik[0]*pik[0]*pik[0]*quot(jm(X[j],jm(km(i,j),km(k,j))),pij)+pij[0]*pij[0]*pij[0]*quot(jm(X[k],jm(km(i,k),km(j,k))),pik)
        out[(65,i)]=(T-V.sc(4)).sc(-1)
    for l in range(3):
        i,j=[t for t in range(3) if t!=l]; e=[EP({})]*3; e[i]=EP({ex(2,0,gp[(j,i)]):P(1)}); e[j]=one(-1)
        x=[[xw[t],(e[t]*xw[t]).sc(-1)] for t in range(3)]; Nn=None
        for (a,b),c in (((0,1),2),((1,2),0),((2,0),1)):
            q=jm(x[c],jp(a,b,e)); Nn=q if Nn is None else add(Nn,q)
        p={(a,b):jp(a,b,e,1) for (a,b) in ((0,1),(0,2),(1,2))}; Pp=jm(jm(p[(0,1)],p[(0,2)]),p[(1,2)])
        A=[t.sc(3*fac) for t in jm(Nn,Nn)]; X=[jm(t,t) for t in x]; km=lambda b,a: sub(jp(b,a,e),jp(b,a,e,1))
        for t in range(3):
            b,c=[s for s in range(3) if s!=t]
            q=jm(jm(X[t],jm(km(b,t),km(c,t))),p[(b,c)]); A=[s-r.sc(4) for s,r in zip(A,q)]
        out[(64,l)]=A[1]*Pp[0]-A[0]*Pp[1]
    return out
if __name__=="__main__":
    for key,f in sorted(nums().items(),reverse=True):
        us={(k[0],k[1]) for k in f.t}; vs={(k[2],k[3]) for k in f.t}
        g=0
        for c in f.t.values(): g=c.gcd(g) if g!=0 else c
        print(key,"terms",len(f.t),"u-exponents",len(us),"v-exponents",len(vs),"max |coef|",max(abs(int(x)) for c in f.t.values() for x in c.coeffs()),"d-degree",max(c.degree() for c in f.t.values()),"content",g.factor())
