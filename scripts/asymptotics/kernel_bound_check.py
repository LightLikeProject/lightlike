"""Bound on Racah's kernel by its Stirling exponent (numerical evidence, not a proof).

Checks the statements of Lightlike/Asymptotics/KernelBound.lean. Racah's kernel is
f(z) = pi T(z) / sin(pi z) with T(z) = Gamma(z + 2) / (prod_i Gamma(z - a_i + 1)
prod_k Gamma(b_k - z + 1)), for face sums a_i and quadrilateral sums b_k of integer spins J. With
F(w) = w log w - w (principal logarithm), sigma = z + 3/2, A = a + 3/2, B = b + 2:

  kernelExp(A, B, sigma) = Re F(sigma) - sum_i Re F(sigma - A_i + 1/2) - sum_k Re F(B_k - sigma)
                           - pi Im sigma.

  (K1) Re(u log u) <= Re((u + 1/2) log(u + 1/2)) + log 2 on a grid of the whole plane, with
       equality at u = -1/4 (re_xlog_le_re_xlog_add_half);
  (K2) for the spins lambda (1, ..., 1) and lambda (1, 2, 2, 1, 2, 2), lambda = 1, 5, 20, 50, and
       c = 1/2, the ratios |f(z)| / exp(kernelExp) and |f(z)| / exp(Re phaseC(A, B, z + 3/2))
       on grids of the three regions Im z >= c; -3/2 <= Re z <= a_i - 1/2; Re z >= b_k + 1/2
       (with 0 < Im z < c in the last two) stay below a constant that does not grow with lambda
       (exists_norm_racahKernel_le_kernelExp, exists_norm_racahKernel_le);
  (K3) kernelExp(A_l, B_l, sigma) <= Re psi_l(sigma) + 2 + 4 log 2 for random real lengths l and
       random sigma in the whole plane, psi_l the phase of Saddle.lean (kernelExp_le_re_phase).

Controls (must FAIL):
  * (K1) without the term log 2, at u = -1/4;
  * the kernel bound in the gap max_i a_i - 1/2 < Re z < min_k b_k + 1/2 close to the real axis:
    at an integer n of the gap, |f(n + i eps)| / exp(kernelExp) grows like 1/eps, so the three
    regions of the statement are needed.
Run: .venv/bin/python -I scripts/asymptotics/kernel_bound_check.py   (expect "RESULT: OK")
"""
import random

from mpmath import mp, mpf, mpc, pi, log, exp, sin, loggamma, re, im, fabs

mp.dps = 30
random.seed(2)
I = mpc(0, 1)


def F(w):
    return w * log(w) - w if w != 0 else mpc(0)


def xlog(w):
    return w * log(w) if w != 0 else mpc(0)


def face(l):
    return [l[0] + l[1] + l[2], l[0] + l[4] + l[5], l[3] + l[1] + l[5], l[3] + l[4] + l[2]]


def quad(l):
    return [l[0] + l[1] + l[3] + l[4], l[1] + l[2] + l[4] + l[5], l[2] + l[0] + l[5] + l[3]]


def log_kernel(a, b, z):
    """log |f(z)| for Im z > 0, from log-Gamma, so that large spins do not overflow."""
    s = log(pi) + re(loggamma(z + 2))
    s -= sum(re(loggamma(z - ai + 1)) for ai in a)
    s -= sum(re(loggamma(bk - z + 1)) for bk in b)
    return s - log(fabs(sin(pi * z)))


def kernel_exp(A, B, sig):
    return (re(F(sig)) - sum(re(F(sig - Ai + mpf(1) / 2)) for Ai in A)
            - sum(re(F(Bk - sig)) for Bk in B) - pi * im(sig))


def re_phaseC(A, B, sig):
    v = (xlog(sig) - sum(xlog(sig - Ai) for Ai in A) + sum(xlog(sig - Bk) for Bk in B)
         - 2 * pi * I * sig + pi * I * sum(B))
    return re(v)


def re_phase(l, x):
    A, B = face(l), quad(l)
    v = (xlog(x) - sum(xlog(x - Ai) for Ai in A) - sum(xlog(Bk - x) for Bk in B) + pi * I * x)
    return re(v)


def region_points(a, b, c):
    """Points of the three regions of the kernel bound."""
    lo, hi = mpf(-3) / 2, max(b) + 6
    pts = []
    for k in range(60):
        x = lo + (hi - lo) * mpf(k) / 59
        for y in (c, mpf(1), mpf(3), mpf(10)):
            pts.append(mpc(x, y))
    for y in (mpf('1e-6'), mpf('1e-3'), mpf('0.1'), mpf('0.4')):
        amax = max(a)
        for k in range(40):
            x = lo + (amax - mpf(1) / 2 - lo) * mpf(k) / 39
            pts.append(mpc(x, y))
        for n in range(-1, amax):
            pts.append(mpc(n, y))
        bmin = min(b)
        for k in range(40):
            pts.append(mpc(bmin + mpf(1) / 2 + mpf(k) / 4, y))
            pts.append(mpc(bmin + 1 + k, y))
    return pts


def main():
    ok = True
    worst = mpf(-100)
    for k in range(201):
        for m in range(201):
            u = mpc(mpf(-5) + mpf(k) / 20, mpf(-5) + mpf(m) / 20)
            worst = max(worst, re(xlog(u)) - re(xlog(u + mpf(1) / 2)) - log(2))
    u0 = mpf(-1) / 4
    at = re(xlog(u0)) - re(xlog(u0 + mpf(1) / 2)) - log(2)
    k1 = worst <= mpf('1e-25') and fabs(at) < mpf('1e-25')
    print(f"(K1) max of Re xlog(u) - Re xlog(u + 1/2) - log 2 on a 201 x 201 grid of [-5, 5]^2: "
          f"{mp.nstr(worst, 6)}; at u = -1/4: {mp.nstr(at, 3)}: {'OK' if k1 else 'FAIL'}")
    ok &= k1
    c = mpf(1) / 2
    for base in ([1] * 6, [1, 2, 2, 1, 2, 2]):
        r1, r2 = [], []
        for lam in (1, 5, 20, 50):
            J = [lam * x for x in base]
            a, b = face(J), quad(J)
            A = [ai + mpf(3) / 2 for ai in a]
            B = [bk + 2 for bk in b]
            pts = region_points(a, b, c)
            m1 = max(log_kernel(a, b, z) - kernel_exp(A, B, z + mpf(3) / 2) for z in pts)
            m2 = max(log_kernel(a, b, z) - re_phaseC(A, B, z + mpf(3) / 2) for z in pts)
            r1.append(exp(m1))
            r2.append(exp(m2))
        k2 = max(r1) < 100 and max(r2) < 100 * exp(2 + 4 * log(2)) and max(r1) < 2 * min(r1) and max(r2) < 2 * min(r2)
        print(f"(K2) J = lambda {base}, lambda = 1, 5, 20, 50: sup |f| / exp(kernelExp) = "
              f"{', '.join(mp.nstr(r, 4) for r in r1)}; sup |f| / exp(Re phaseC) = "
              f"{', '.join(mp.nstr(r, 4) for r in r2)}: {'OK' if k2 else 'FAIL'}")
        ok &= k2
    worst = mpf(-100)
    for _ in range(400):
        l = [mpf(random.uniform(0.5, 30)) for _ in range(6)]
        x = mpc(random.uniform(-10, 100), random.uniform(-20, 20))
        A, B = face(l), quad(l)
        worst = max(worst, kernel_exp(A, B, x) - re_phase(l, x))
    k3 = worst <= 2 + 4 * log(2)
    print(f"(K3) max of kernelExp - Re psi over 400 random lengths and points: {mp.nstr(worst, 6)} "
          f"<= 2 + 4 log 2 = {mp.nstr(2 + 4 * log(2), 6)}: {'OK' if k3 else 'FAIL'}")
    ok &= k3
    c1 = at + log(2) > 0
    print(f"control (K1 without log 2, at u = -1/4): Re xlog(u) - Re xlog(u + 1/2) = "
          f"{mp.nstr(at + log(2), 6)} > 0: {'fails as it must' if c1 else 'UNEXPECTED PASS'}")
    ok &= c1
    J = [5] * 6
    a, b = face(J), quad(J)
    A = [ai + mpf(3) / 2 for ai in a]
    B = [bk + 2 for bk in b]
    n = (max(a) + min(b)) // 2
    rat = [exp(log_kernel(a, b, mpc(n, e)) - kernel_exp(A, B, mpc(n, e) + mpf(3) / 2))
           for e in (mpf('1e-3'), mpf('1e-6'))]
    c2 = rat[1] > 100 * rat[0]
    print(f"control (gap, J = 5 (1, ..., 1), z = {n} + i eps): |f| / exp(kernelExp) = "
          f"{mp.nstr(rat[0], 4)} at eps = 1e-3, {mp.nstr(rat[1], 4)} at eps = 1e-6: "
          f"{'fails as it must' if c2 else 'UNEXPECTED PASS'}")
    ok &= c2
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
