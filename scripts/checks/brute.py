"""Brute-force scalar curvature of a monotone metric on the faithful states D^1_n.

Chart: rho = rho0 + sum_a x_a T_a with T_a a basis of traceless Hermitian matrices (D^1 is an
open subset of an affine hyperplane, so this is a global chart).  Metric
    g_rho(X, Y) = Re sum_{kl} c(mu_k, mu_l) conj(X~_kl) Y~_kl,   X~ = V* X V,  rho = V diag(mu) V*.
Derivatives by central finite differences in mpmath; curvature from the coordinate formula.
"""
import mpmath as mp

mp.mp.dps = 70


def c_wyd(beta):
    """Morozova-Chentsov function of WYD(beta), normalized c(x, x) = 1/x."""
    beta = mp.mpf(beta)

    def c(x, y):
        if abs(x - y) < mp.mpf(10) ** (-(mp.mp.dps // 2)):
            # c(x, y) -> 1/x; second-order correction is negligible at this separation
            return 1 / x
        return ((x ** beta - y ** beta) * (x ** (1 - beta) - y ** (1 - beta))
                / (beta * (1 - beta) * (x - y) ** 2))
    return c


def c_bkm(x, y):
    if abs(x - y) < mp.mpf(10) ** (-(mp.mp.dps // 2)):
        return 1 / x
    return (mp.log(x) - mp.log(y)) / (x - y)


def basis(n):
    B = []
    for i in range(n):
        for j in range(i + 1, n):
            A = mp.zeros(n, n); A[i, j] = 1; A[j, i] = 1; B.append(A)
            A = mp.zeros(n, n); A[i, j] = -1j; A[j, i] = 1j; B.append(A)
    for i in range(n - 1):
        A = mp.zeros(n, n); A[i, i] = 1; A[n - 1, n - 1] = -1; B.append(A)
    return B


def metric(rho, B, c):
    n = rho.rows
    mu, V = mp.eighe(rho) if hasattr(mp, "eighe") else mp.eigh(rho)
    Vh = V.H
    Bt = [Vh * T * V for T in B]
    C = [[c(mu[k], mu[l]) for l in range(n)] for k in range(n)]
    N = len(B)
    g = mp.zeros(N, N)
    for a in range(N):
        for b in range(a, N):
            s = 0
            for k in range(n):
                for l in range(n):
                    s += C[k][l] * mp.conj(Bt[a][k, l]) * Bt[b][k, l]
            g[a, b] = g[b, a] = mp.re(s)
    return g


def scal(lam, c, h=None):
    n = len(lam)
    if h is None:
        h = mp.mpf("1e-14") * min(mp.mpf(x) for x in lam)
    rho0 = mp.diag([mp.mpf(x) for x in lam])
    B = basis(n)
    N = len(B)
    G = lambda *pairs: metric(rho0 + sum((s * B[a] for a, s in pairs), mp.zeros(n, n)), B, c)
    g0 = G()
    gp = [G((a, h)) for a in range(N)]
    gm = [G((a, -h)) for a in range(N)]
    dg = [(gp[a] - gm[a]) / (2 * h) for a in range(N)]  # dg[a][b,c] = d_a g_bc
    ddg = [[None] * N for _ in range(N)]
    for a in range(N):
        ddg[a][a] = (gp[a] - 2 * g0 + gm[a]) / h ** 2
        for b in range(a + 1, N):
            M = (G((a, h), (b, h)) - G((a, h), (b, -h)) - G((a, -h), (b, h))
                 + G((a, -h), (b, -h))) / (4 * h * h)
            ddg[a][b] = ddg[b][a] = M
    gi = g0 ** -1
    # Christoffel of the first kind: Gam1[c][a][b] = 1/2 (d_a g_bc + d_b g_ac - d_c g_ab)
    Gam1 = [[[(dg[a][b, cc] + dg[b][a, cc] - dg[cc][a, b]) / 2 for b in range(N)]
             for a in range(N)] for cc in range(N)]
    Gam = [[[sum(gi[e, cc] * Gam1[cc][a][b] for cc in range(N)) for b in range(N)]
            for a in range(N)] for e in range(N)]
    S = 0
    for a in range(N):
        for b in range(N):
            for cc in range(N):
                for d in range(N):
                    w = gi[a, cc] * gi[b, d]
                    if w == 0:
                        continue
                    R = (ddg[b][cc][a, d] + ddg[a][d][b, cc] - ddg[a][cc][b, d]
                         - ddg[b][d][a, cc]) / 2
                    R += sum(Gam1[f][a][d] * Gam[f][b][cc] - Gam1[f][a][cc] * Gam[f][b][d]
                             for f in range(N))
                    S += w * R
    return S


if __name__ == "__main__":
    import sys, time
    t = time.time()
    print("BKM uniform n=3 (expect 5):", mp.nstr(scal(["0.335", "0.333", "0.332"], c_bkm), 12))
    print("BKM (0.5,0.4,0.1) (Petz: 1.16438):", mp.nstr(scal(["0.5", "0.4", "0.1"], c_bkm), 12))
    print("WY (0.5,0.4,0.1):", mp.nstr(scal(["0.5", "0.4", "0.1"], c_wyd("0.5")), 12))
    print("WY (0.7,0.2,0.1):", mp.nstr(scal(["0.7", "0.2", "0.1"], c_wyd("0.5")), 12))
    print("WYD beta=0.999 (0.5,0.4,0.1):", mp.nstr(scal(["0.5", "0.4", "0.1"], c_wyd("0.999")), 12))
    print("time", time.time() - t)
