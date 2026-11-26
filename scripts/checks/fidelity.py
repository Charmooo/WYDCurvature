"""Is the Lean statement about the paper's object?  Three independent computations of the scalar curvature at a NON-diagonal state:
 A  the Lean definitions, literally: matPow = exp(s*log), chart z -> (rho^b, rho^(1-b)), pullback of wydPairing (Frechet derivative by the
    2x2 block trick), christoffelForm, christoffel, riemann, ricci, scalarCurvature (derivatives of the metric by high-precision differences)
 B  the paper: metric Tr(A c_f(L,R) B), c = 1/(y f(x/y)), f = f_p of Definition 6.1; same curvature code but a different metric code
 C  the paper's Theorem 5.3 with h of (5.1) from c_f (derivative of log c symbolic-free, by mp.diff), no curvature code at all
 D  the closed form proved in Lean (curvSum with wydHs + (n^2-1)(n^2-2)/4), through kappa"""
import mpmath as mp, random, sys, itertools
from multiprocessing import Pool
mp.mp.dps=50
def herm_basis(n):
    B=[]
    for i in range(n):
        for j in range(i+1,n):
            M=mp.zeros(n); M[i,j]=M[j,i]=1; B.append(M)
            M=mp.zeros(n); M[i,j]=mp.mpc(0,-1); M[j,i]=mp.mpc(0,1); B.append(M)
    for i in range(n-1):
        M=mp.zeros(n); M[i,i]=1; M[i+1,i+1]=-1; B.append(M)
    return B
def eigh(A): return mp.eighe(A)
def metricA(rho,B,b):
    n=rho.rows; E,U=eigh(rho); UH=U.H
    def dpow(s):       # Frechet derivatives of x^s via divided differences of exp(s log): Daleckii-Krein would share code with B; use the block trick instead
        out=[]
        for X in B:
            # derivative of the matrix function at rho in direction X through a resolvent-free difference quotient with Richardson (order 8)
            h=mp.mpf(10)**(-6); 
            def f(t):
                e,u=eigh(rho+t*X); return u*mp.diag([mp.exp(s*mp.log(x)) for x in e])*u.H
            D=mp.zeros(n); co=[mp.mpf(4)/5,-mp.mpf(1)/5,mp.mpf(4)/105,-mp.mpf(1)/280]
            for k,c in enumerate(co,1): D+=c*(f(k*h)-f(-k*h))/h
            out.append(D)
        return out
    P=dpow(b); Q=dpow(1-b); N=len(B); G=mp.zeros(N)
    tr=lambda X,Y: mp.re(sum(X[i,k]*Y[k,i] for i in range(n) for k in range(n)))
    for i in range(N):
        for j in range(N): G[i,j]=(tr(P[i],Q[j])+tr(P[j],Q[i]))/(2*b*(1-b))
    return G
def fp(x,b):
    p=1/b; pt=1/(1-b)
    return mp.mpf(1) if x==1 else (x-1)**2/(p*pt*(x**(1/p)-1)*(x**(1/pt)-1))
def cf(x,y,b): return 1/(y*fp(x/y,b)) if x!=y else 1/x
def metricB(rho,B,b):
    n=rho.rows; E,U=eigh(rho); C=[[cf(E[i],E[j],b) if abs(E[i]-E[j])>mp.mpf(10)**-30 else 1/E[i] for j in range(n)] for i in range(n)]
    T=[U.H*X*U for X in B]; N=len(B); G=mp.zeros(N)
    for i in range(N):
        for j in range(N): G[i,j]=mp.re(sum(T[i][k,l]*C[l][k]*T[j][l,k] for k in range(n) for l in range(n)))
    return G
def scal(metric,rho,b,h):
    """Lean: christoffelForm, riemann, ricci, scalarCurvature, with D and D2 of G by central differences (order 4)."""
    n=rho.rows; B=herm_basis(n); N=len(B)
    g=lambda v: metric(rho+sum((v[i]*B[i] for i in range(N) if v[i]!=0),mp.zeros(n)),B,b)
    z=[mp.mpf(0)]*N; G=g(z); Gi=G**-1
    def e(*idx):
        v=list(z)
        for i,c in idx: v[i]+=c*h
        return v
    co=[(1,mp.mpf(2)/3),(2,-mp.mpf(1)/12)]
    pts={}
    def ev(*idx):
        key=tuple(e(*idx))
        if key not in pts: pts[key]=g(list(key))
        return pts[key]
    D=[sum((c*(ev((i,k))-ev((i,-k))) for k,c in co),mp.zeros(N))/h for i in range(N)]
    D2={}
    for i in range(N):
        for j in range(i,N):
            if i==j: M=(-ev((i,2))+16*ev((i,1))-30*G+16*ev((i,-1))-ev((i,-2)))/(12*h*h)
            else: M=sum((c*c2*(ev((i,k),(j,l))-ev((i,k),(j,-l))-ev((i,-k),(j,l))+ev((i,-k),(j,-l))) for k,c in co for l,c2 in co),mp.zeros(N))/(h*h)
            D2[i,j]=D2[j,i]=M
    # christoffelForm v w u = (D v w u + D w v u - D u v w)/2
    cfm=lambda v,w,u: (D[v][w,u]+D[w][v,u]-D[u][v,w])/2
    Gam=[[[mp.fsum(Gi[k,u]*cfm(v,w,u) for u in range(N)) for k in range(N)] for w in range(N)] for v in range(N)]
    # D Gam: derivative of Gi*form
    dGi=[-(Gi*D[a]*Gi) for a in range(N)]
    F=[[[cfm(v,w,u) for u in range(N)] for w in range(N)] for v in range(N)]
    def dF(a,v,w,u): return (D2[a,v][w,u]+D2[a,w][v,u]-D2[a,u][v,w])/2
    dG=[[[[mp.fsum(dGi[a][k,u]*F[v][w][u]+Gi[k,u]*dF(a,v,w,u) for u in range(N)) for k in range(N)] for w in range(N)] for v in range(N)] for a in range(N)]
    # riemann X Y Z = DGam X Y Z - DGam Y X Z + Gam X (Gam Y Z) - Gam Y (Gam X Z); ricci Y Z = trace X -> R X Y Z
    Ric=mp.zeros(N)
    for y in range(N):
        for w in range(N):
            Ric[y,w]=mp.fsum(dG[x][y][w][x]-dG[y][x][w][x]+mp.fsum(Gam[x][m][x]*Gam[y][w][m]-Gam[y][m][x]*Gam[x][w][m] for m in range(N)) for x in range(N))
    return mp.fsum(Gi[i,j]*Ric[j,i] for i in range(N) for j in range(N))
def thm53(E,b):
    n=len(E); c=lambda x,y: cf(x,y,b)
    lc=lambda z,x: mp.diff(lambda s: mp.log(c(s,x)),z)
    def h(x,y,z):
        h1=(c(x,y)-z*c(x,z)*c(y,z))/((x-z)*(y-z)*c(x,z)*c(y,z))
        h2=(c(x,z)-c(y,z))**2/((x-y)**2*c(x,y)*c(x,z)*c(y,z))
        h3=z*(lc(z,x)-lc(z,y))/(x-y); h4=z*lc(z,x)*lc(z,y)
        return h1-h2/2+2*h3-h4
    ep=mp.mpf(10)**-14     # coincident arguments: symmetric limits by averaging +- perturbations (error ep^2)
    def H(x,y,z):
        if x!=y and y!=z and x!=z: return h(x,y,z)
        return (h(x*(1+ep),y*(1+2*ep),z*(1-3*ep))+h(x*(1-ep),y*(1-2*ep),z*(1+3*ep)))/2 
    return mp.fsum(H(x,y,z) for x in E for y in E for z in E)-mp.fsum(H(x,x,x) for x in E)+mp.mpf((n*n-1)*(n*n-2))/4
def closed(E,b):
    n=len(E); d=2*b-1
    kap=lambda t:(1-b)/(t**(1-b)-1)-b/(t**b-1)
    def kp(a,c): return kap(c/a) if a!=c else (1-2*b)/(-2)
    S=mp.mpf((n*n-1)*(n*n-2))/4
    for a in range(n):
        ks=[kp(E[a],E[c]) for c in range(n) if c!=a]; K=mp.fsum(ks); S+=(mp.mpf(3)/2*mp.fsum(x*x for x in ks)-K*K+(1-2*b)*K)/E[a]
    P=[x**b for x in E]; Q=[x**(1-b) for x in E]; DD=lambda i,j:(P[i]-P[j])*(Q[i]-Q[j])
    for i,j,k in itertools.combinations(range(n),3):
        A=(P[j]-P[i])*(Q[k]-Q[i])-(P[k]-P[i])*(Q[j]-Q[i]); S+=3*b*(1-b)*A*A/(DD(i,j)*DD(i,k)*DD(j,k))
    return S
def rnd_state(n,rng):
    M=mp.zeros(n)
    for i in range(n):
        for j in range(n): M[i,j]=mp.mpc(rng.gauss(0,1),rng.gauss(0,1))
    R=M*M.H+mp.mpf(rng.choice([.05,.3,1]))*mp.eye(n); t=mp.re(sum(R[i,i] for i in range(n))); return R/t
def job(a):
    n,b,seed=a; rng=random.Random(seed); rho=rnd_state(n,rng); b=mp.mpf(b); E=[mp.re(x) for x in mp.eighe(rho,eigvals_only=True)]
    B=scal(metricB,rho,b,mp.mpf(10)**-8); A=scal(metricA,rho,b,mp.mpf(10)**-4) if n==2 or (n==3 and seed==0) else None
    GA=metricA(rho,herm_basis(n),b); GB=metricB(rho,herm_basis(n),b)
    return n,str(b),seed,A,B,thm53(E,b),closed(E,b),max(abs(GA[i,j]-GB[i,j]) for i in range(GA.rows) for j in range(GA.cols))
if __name__=="__main__":
    n=int(sys.argv[1]); bs=sys.argv[2].split(','); seeds=range(int(sys.argv[3]))
    with Pool(4) as p:
        for n,b,s,A,B,T,C,dm in p.imap(job,[(n,b,s) for b in bs for s in seeds]):
            r=lambda x: mp.nstr(abs(x/C-1),2)
            print(f"n={n} beta={b:>5} S={mp.nstr(C,12):>16}  rel.diff from closed form:  Lean defs {r(A) if A is not None else '   -  '}  paper metric {r(B)}  Theorem 5.3 {r(T)}  metric entries {mp.nstr(dm,2)}",flush=True)
