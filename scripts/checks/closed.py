"""Closed form for the WYD(beta) scalar curvature via its Hessian structure.

WYD(beta) is the Hessian of Phi(u) = Tr u^(1/beta) / (1 - beta) in the coordinates u = rho^beta.
At a diagonal state, with phi(mu) = mu^(1/beta - 1) / (beta (1 - beta)) (so phi(lam^beta) = lam^(1-beta)/(beta(1-beta))):
    w(x, y)    = phi^[1](x^b, y^b)          metric weights
    F(x, y, z) = phi^[2](x^b, y^b, z^b)      third derivative of Phi
    h(x, y, z) = F(x,y,z)^2 / (2 w(x,y) w(y,z) w(z,x)) - F(x,x,y) F(x,x,z) / (w(x,y) w(x,z) w(x,x))
    S^1 = sum_{ijk} h - sum_i h(l_i, l_i, l_i) + (n^2 - 1)(n^2 - 2)/4.
Divided differences use small distinct perturbations for coincident arguments, at high precision.
"""
import mpmath as mp

mp.mp.dps = 80
EPS = mp.mpf(10) ** -30


class WYD:
    def __init__(self, beta):
        self.b = mp.mpf(beta)
        b = self.b
        self.k = 1 / (b * (1 - b))

    def phi_l(self, x):  # phi at mu = x^b, written in lambda
        return self.k * x ** (1 - self.b)

    def mu(self, x):
        return x ** self.b

    def w(self, x, y):
        if x == y:
            y = y * (1 + EPS)
        return (self.phi_l(x) - self.phi_l(y)) / (self.mu(x) - self.mu(y))

    def F(self, x, y, z):
        # perturb coincident arguments so the three are distinct
        if x == y:
            y = y * (1 + EPS)
        if x == z or y == z:
            z = z * (1 - 2 * EPS)
        if x == z:
            z = z * (1 - 3 * EPS)
        mx, my, mz = self.mu(x), self.mu(y), self.mu(z)
        d1 = lambda a, ma, c, mc: (self.phi_l(a) - self.phi_l(c)) / (ma - mc)
        return (d1(x, mx, y, my) - d1(x, mx, z, mz)) / (my - mz)

    def h(self, x, y, z):
        w, F = self.w, self.F
        return (F(x, y, z) ** 2 / (2 * w(x, y) * w(y, z) * w(z, x))
                - F(x, x, y) * F(x, x, z) / (w(x, y) * w(x, z) * w(x, x)))

    def hs(self, x, y, z):
        return (self.h(x, y, z) + self.h(y, z, x) + self.h(z, x, y)) / 3

    def scal(self, lam):
        lam = [mp.mpf(v) for v in lam]
        n = len(lam)
        return (sum(self.hs(a, b, c) for a in lam for b in lam for c in lam)
                - sum(self.hs(a, a, a) for a in lam) + mp.mpf((n * n - 1) * (n * n - 2)) / 4)


if __name__ == "__main__":
    import os, sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import brute
    for beta in ["0.999999", "0.75", "0.55", "1.5", "2"]:
        for lam in [["0.5", "0.4", "0.1"], ["0.7", "0.2", "0.1"], ["0.4", "0.3", "0.2", "0.1"]]:
            mp.mp.dps = 80
            cf = WYD(beta).scal(lam)
            mp.mp.dps = 70
            bf = brute.scal(lam, brute.c_wyd(beta))
            print(beta, lam, mp.nstr(cf, 15), mp.nstr(bf, 15), mp.nstr(cf - bf, 3))
