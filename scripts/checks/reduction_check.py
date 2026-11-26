"""Checks of every identity stated in reduction.tex.  Symbolic where possible (sympy, exact), otherwise mpmath.
Labels follow the document."""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp, mpmath as mp
OK = []
def rep(name, ok, extra=""):
    OK.append(bool(ok)); print(("ok   " if ok else "FAIL ") + name, extra, flush=True)
b = sp.Symbol("beta"); P = sp.symbols("P1:4", positive=True); Q = sp.symbols("Q1:4", positive=True)
def w(i, j): return Q[i]/(b**2*P[i]) if i == j else (Q[i]-Q[j])/(b*(1-b)*(P[i]-P[j]))
def Fiij(i, j): return (w(i, i)-w(i, j))/(P[i]-P[j])
F123 = (w(0, 1)-w(0, 2))/(P[1]-P[2])
kap = lambda i, j: (1-b)*Q[i]/(Q[j]-Q[i]) - b*P[i]/(P[j]-P[i])
z = lambda e: sp.simplify(sp.together(e)) == 0
# --- section 1-2: phi and its divided differences
m = sp.Symbol("mu", positive=True); ph = m**(1/b-1)/(b*(1-b))
rep("phi' = mu^(1/b-2)/b^2, F_iii = (1-2b)/(2 b mu) phi'", z(sp.diff(ph, m)-m**(1/b-2)/b**2) and z(sp.powsimp(sp.diff(ph, m, 2)/2-(1-2*b)/(2*b*m)*sp.diff(ph, m))))
rep("F_iij/w_ij = -kappa_ij/(b P_i)", z(Fiij(0, 1)/w(0, 1)+kap(0, 1)/(b*P[0])))
A = sp.Matrix([[1, 1, 1], list(P), list(Q)]).det(); D = lambda i, j: (P[i]-P[j])*(Q[i]-Q[j])
rep("F_123 = A/(b(1-b) V)", z(F123-A/(b*(1-b)*(P[1]-P[0])*(P[2]-P[0])*(P[2]-P[1]))))
rep("T1 = b(1-b)A^2/(2DDD)", z(F123**2/(2*w(0, 1)*w(1, 2)*w(2, 0))-b*(1-b)*A**2/(2*D(0, 1)*D(1, 2)*D(2, 0))))
rep("vertex term = kap kap/lam", z(Fiij(0, 1)*Fiij(0, 2)/(w(0, 1)*w(0, 2)*w(0, 0))-kap(0, 1)*kap(0, 2)/(P[0]*Q[0])))
# two-point function
Faaa = (1-2*b)/(2*b*P[0])*w(0, 0)
haab = Fiij(0, 1)**2/(2*w(0, 0)*w(0, 1)**2) - Faaa*Fiij(0, 1)/(w(0, 0)*w(0, 1)*w(0, 0))
hbaa = Fiij(0, 1)**2/(2*w(0, 0)*w(0, 1)**2) - Fiij(1, 0)**2/(w(0, 1)**2*w(1, 1))
q = (2*haab+hbaa)/3; kab, kba = kap(0, 1), kap(1, 0); xa, xb = P[0]*Q[0], P[1]*Q[1]
rep("hs(a,a,b) two-point formula (exact in beta)", z(q-((kab**2/2+(1-2*b)/3*kab)/xa-kba**2/(3*xb))))
rep("kap_ab + kap_ba = 2b-1", z(kab+kba-(2*b-1)))
# --- phi-hat form and gy form: exponentials
d, s = sp.symbols("d s", positive=True)
fh = (sp.sinh(s)-sp.sinh(d*s)/d)/(1-d**2); fp = (sp.cosh(s)-sp.cosh(d*s))/(1-d**2)
ex = lambda e: sp.simplify(sp.expand(sp.together(e.rewrite(sp.exp))))
rep("phihat' = d/ds phihat, phihat'' = d^2 phihat + sinh", ex(sp.diff(fh, s)-fp) == 0 and ex(sp.diff(fp, s)-d**2*fh-sp.sinh(s)) == 0)
mp.mp.dps = 60; random.seed(5); worst = {}
def upd(k, v): worst[k] = max(worst.get(k, mp.mpf(0)), abs(v))
def phih(t, d): return (mp.sinh(t)-mp.sinh(d*t)/d)/(1-d*d)
def phip(t, d): return (mp.cosh(t)-mp.cosh(d*t))/(1-d*d)
for _ in range(300):
    d_ = mp.mpf(random.uniform(-3, 3)); be = (1+d_)/2; sg = sorted(mp.mpf(random.uniform(-3, 3)) for _ in range(3)); lam = [mp.exp(2*x) for x in sg]
    PP = [x**be for x in lam]; QQ = [x**(1-be) for x in lam]; K = lambda t: phih(t, d_)/phip(t, d_)
    dl = lambda i, j: sg[i]-sg[j]; DD = lambda i, j: (PP[i]-PP[j])*(QQ[i]-QQ[j]); AA = sum(PP[i]*QQ[j]-PP[j]*QQ[i] for i, j in ((0, 1), (1, 2), (2, 0)))
    upd("A = -2d(1-d^2) sum", AA/(-2*d_*(1-d_**2)*sum(mp.exp(sg[i]+sg[j])*phih(dl(i, j), d_) for i, j in ((0, 1), (1, 2), (2, 0))))-1)
    upd("D_ij = 2(1-d^2) e phihat'", DD(0, 1)/(2*(1-d_**2)*mp.exp(sg[0]+sg[1])*phip(dl(0, 1), d_))-1)
    ka = lambda i, j: (1-be)*QQ[i]/(QQ[j]-QQ[i])-be*PP[i]/(PP[j]-PP[i])
    upd("kappa = (d/2)(1-K)", ka(0, 1)/(d_/2*(1-K(sg[1]-sg[0])))-1)
    T1 = be*(1-be)*AA**2/(2*DD(0, 1)*DD(1, 2)*DD(2, 0)); V = sum(ka(a, (a+1) % 3)*ka(a, (a+2) % 3)/lam[a] for a in range(3)); hs = T1-V/3
    x = [mp.exp(-t) for t in sg]; N = x[2]*phih(dl(0, 1), d_)+x[0]*phih(dl(1, 2), d_)+x[1]*phih(dl(2, 0), d_)
    H = N**2/(16*phip(dl(0, 1), d_)*phip(dl(1, 2), d_)*phip(dl(2, 0), d_))-sum(x[a]**2*(K(sg[(a+1) % 3]-sg[a])-1)*(K(sg[(a+2) % 3]-sg[a])-1) for a in range(3))/12
    upd("hs = d^2 H", (hs-d_**2*H)/(abs(T1)+abs(V)))
    B = lambda k, t: k/mp.expm1(k*t)
    def g4(t): return B(1-d_, t), B(1-d_, t)+1-d_, B(1+d_, t), B(1+d_, t)+1+d_   # y, g, G, Y
    u, v = sg[1]-sg[0], sg[2]-sg[1]; (yu, gu, Gu, Yu), (yv, gv, Gv, Yv), (yw, gw, Gw, Yw) = g4(u), g4(v), g4(u+v); Pi, Th = Yu+Gv, gu+yv; X = [1/t for t in lam]
    upd("p = d(1-K), m = d(1+K)", max(abs((yu-Gu)/(d_*(1-K(u)))-1), abs((Yu-gu)/(d_*(1+K(u)))-1)))
    upd("gy form of 96 hs", (96*hs-(12*X[1]*(Yu*yv-gu*Gv)**2/(Pi*Th)-8*(X[0]*(yu-Gu)*(yw-Gw)+X[1]*(Yu-gu)*(yv-Gv)+X[2]*(Yv-gv)*(Yw-gw))))/(96*(abs(T1)+abs(V))))
    upd("w-gap addition", max(abs(yw*Th/(yu*yv)-1), abs(gw*Th/(gu*gv)-1), abs(Yw*Pi/(Yu*Yv)-1), abs(Gw*Pi/(Gu*Gv)-1)))
    # qubit and psi forms
    t = mp.mpf(random.uniform(.1, 5)); k_ = K(t); xx, yy = 1/(1+mp.exp(2*t)), mp.exp(2*t)/(1+mp.exp(2*t)); dn = -d_
    kf = lambda r: (1-be)/(r**(1-be)-1)-be/(r**be-1); qf = lambda a, b_: (kf(b_/a)**2/2+dn/3*kf(b_/a))/a-kf(a/b_)**2/(3*b_)
    J = k_*mp.cosh(t)+mp.sinh(t)
    upd("3(q+q) = (d^2/2)(J^2-4cosh^2+1)", 3*(qf(xx, yy)+qf(yy, xx))/(d_**2/2*(J*J-4*mp.cosh(t)**2+1))-1)
    L = mp.mpf(random.uniform(.3, 3)); a_ = L*mp.exp(-2*t); psi = mp.exp(2*t)*(k_-1)*(3*k_+1)-2*(k_+1)**2
    upd("q = d^2 psi/(24 lam)", qf(a_, L)/(d_**2*psi/(24*L))-1)
for k_, v_ in worst.items(): rep(k_, v_ < mp.mpf(10)**-35, mp.nstr(v_, 3))
# --- remaining identities of sections 5-6: derivative rules, omega and G', W'/phihat''
k = sp.Symbol("k", positive=True); Bk = k/(sp.exp(k*s)-1)
rep("B' = -B(B+k)", sp.simplify(sp.diff(Bk, s)+Bk*(Bk+k)) == 0)
mx = mp.mpf(0); my = mp.mpf(0)
for _ in range(40):
    d_ = mp.mpf(random.uniform(.05, 3)); t = mp.mpf(random.uniform(.2, 4)); Kf = lambda r: phih(r, d_)/phip(r, d_); om = lambda r: mp.sinh(r)-Kf(r)*mp.cosh(r); Gf = lambda r: (Kf(r)*mp.cosh(r)+mp.sinh(r))**2-4*mp.cosh(r)**2
    mx = max(mx, abs(mp.diff(Gf, t)/(-4*om(t)*mp.cosh(t)-2*mp.diff(om, t)*(2*mp.sinh(t)-om(t)))-1))
    Wf = lambda r: phip(r, d_)*mp.sinh(r)-phih(r, d_)*mp.cosh(r); q_ = 1/mp.sinh(d_*t)-d_/mp.sinh(t); my = max(my, abs(mp.diff(Wf, t)/(mp.sinh(d_*t)*mp.sinh(t)/d_)-1), abs(mp.sinh(d_*t)*mp.sinh(t)/d_/(d_**2*phih(t, d_)+mp.sinh(t))/((1-d_**2)/(d_*q_))-1))
rep("G' = -4 omega cosh - 2 omega'(2 sinh - omega)", mx < mp.mpf(10)**-15, mp.nstr(mx, 3)); rep("W' and W'/phihat'' forms", my < mp.mpf(10)**-15, mp.nstr(my, 3))
# --- contraction formula on a random G-orthonormal basis (arbitrary symmetric F, w > 0)
mp.mp.dps = 30; n = 3; rnd = random.Random(2)
W = [[0]*n for _ in range(n)]; FF = {}
for i in range(n):
    for j in range(i, n): W[i][j] = W[j][i] = mp.mpf(rnd.uniform(.5, 2))
for i in range(n):
    for j in range(i, n):
        for k in range(j, n): FF[(i, j, k)] = mp.mpf(rnd.uniform(-1, 1))
f = lambda i, j, k: FF[tuple(sorted((i, j, k)))]
E = []
for i in range(n):
    M = mp.zeros(n); M[i, i] = 1/mp.sqrt(W[i][i]); E.append(M)
    for j in range(i+1, n):
        M = mp.zeros(n); M[i, j] = M[j, i] = 1/mp.sqrt(2*W[i][j]); E.append(M)
        M = mp.zeros(n); M[i, j] = mp.mpc(0, 1)/mp.sqrt(2*W[i][j]); M[j, i] = -M[i, j]; E.append(M)
R = mp.matrix([[rnd.gauss(0, 1) for _ in E] for _ in E]); O, _ = mp.qr(R)          # random orthogonal mixing
E = [sum((O[a, c]*E[c] for c in range(len(E))), mp.zeros(n)) for a in range(len(E))]
C3 = lambda X, Y_, Z: sum(f(i, j, k)*X[i, j]*Y_[j, k]*Z[k, i] for i in range(n) for j in range(n) for k in range(n))
Tt = [[[mp.re(C3(X, Y_, Z)+C3(Y_, X, Z)) for Z in E] for Y_ in E] for X in E]; N_ = len(E); r = range(N_)
T2 = sum(Tt[a][c][e]**2 for a in r for c in r for e in r); tau2 = sum(sum(Tt[a][c][c] for c in r)**2 for a in r)
h = lambda i, j, k: f(i, j, k)**2/(2*W[i][j]*W[j][k]*W[k][i])-f(i, i, j)*f(i, i, k)/(W[i][j]*W[i][k]*W[i][i])
S_ = sum(h(i, j, k) for i in range(n) for j in range(n) for k in range(n))-sum(h(i, i, i) for i in range(n))
rep("(|T|^2-|tau|^2)/4 = sum h - sum h_iii", abs((T2-tau2)/4-S_) < mp.mpf(10)**-25, mp.nstr((T2-tau2)/4-S_, 3))
# --- whole formula against brute-force curvature on D^1, betas never used before
import brute, closed
for be in ("-0.85", "0.31", "1.7"):
    for lam in (["0.61", "0.39"], ["0.55", "0.3", "0.15"]):
        mp.mp.dps = 80; c_ = closed.WYD(be).scal(lam); mp.mp.dps = 70; br = brute.scal(lam, brute.c_wyd(be)); rep(f"S formula vs brute force beta={be} {lam}", abs(c_-br) < mp.mpf(10)**-15, mp.nstr(c_-br, 3))
print("all ok" if all(OK) else "SOME FAILED", len(OK), "checks")
