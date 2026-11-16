"""Numerical check of the mapping of the q-6j boundary evaluation onto Jackson's series (stdlib only).

For the q-Racah sum at the lowest sixth colour `q0 = j1 - j5`, with `x0 = j1 - j2 >= 0`, this
mirrors the Lean definitions `qnum`, `qfact`, `qDelta`, `jOmega`, `Sj`, `Tj` and checks, on every
admissible spin tuple at levels r = 5, 7, 9 (`2 <= j <= ...` up to `2 (r - 2)`):

* with Q = exp(2 pi i / r), a = Q^(x0+1), b = Q^((j1+j2+x0)/2 + 2), c = Q^((x0+j4-j5)/2 + 1) and
  n = (j4 + j5 - x0) / 2, the weighted term jOmega(x0+2k) * Sj(q0, x0+2k)^2 is the value at k = 0
  times Tj Q a b c (Q^n) k (a constant ratio in k);
* the boundary evaluation `QDougall` holds: jOmega(q0) * (sum over k) = 1;
* kappa * (Jackson's right side) * jOmega(q0) = 1, with kappa the value at k = 0.

Control: with `b` replaced by `b * Q` the ratio is no longer constant. This is numerical evidence
for the Lean statements, not a proof. Exit code 1 on failure.
"""
import cmath
import itertools
import math
import sys

TOL = 1e-9


def make(r):
    def qn(n):
        return math.sin(n * math.pi / r) / math.sin(math.pi / r)

    def qf(n):
        p = 1.0
        for k in range(n):
            p *= qn(k + 1)
        return p

    def iq(u):
        if u < 0:
            return 0.0
        f = qf(u)
        return 0.0 if abs(f) < 1e-12 else 1 / f

    def delta(a, b, c):
        s = (a + b + c) // 2
        return math.sqrt(qf(s - a) * qf(s - b) * qf(s - c) / qf(s + 1))

    def omega(a, b, c, d, x):
        return qn(x + 1) * delta(a, b, x) ** 2 * delta(c, d, x) ** 2

    def sr(a1, a2, a3, a4, b1, b2, b3):
        t = 0.0
        for z in range(max(b1, 0) + 1):
            t += ((-1) ** z * qf(z + 1) * iq(z - a1) * iq(z - a2) * iq(z - a3) * iq(z - a4)
                  * iq(b1 - z) * iq(b2 - z) * iq(b3 - z))
        return t

    def sj(j1, j2, j4, j5, q, y):
        return sr((j1 + j2 + y) // 2, (j1 + j5 + q) // 2, (j4 + j2 + q) // 2, (j4 + j5 + y) // 2,
                  (j1 + j2 + j4 + j5) // 2, (y + j2 + j5 + q) // 2, (y + j1 + q + j4) // 2)

    return omega, sj


def adm(r, a, b, c):
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0 and a + b + c <= 2 * (r - 2)


def pk(z, q, k):
    p = 1
    for i in range(k):
        p *= 1 - z * q ** i
    return p


def tj(q, a, b, c, x, k):
    return ((1 - a * q ** (2 * k)) / (1 - a)
            * (pk(a, q, k) * pk(b, q, k) * pk(c, q, k) * pk(1 / x, q, k))
            / (pk(q, q, k) * pk(a * q / b, q, k) * pk(a * q / c, q, k) * pk(a * q * x, q, k))
            * (a * q * x / (b * c)) ** k)


def cases(r):
    for j1, j2, j4, j5 in itertools.product(range(2 * (r - 2) + 1), repeat=4):
        q0, x0 = j1 - j5, j1 - j2
        if q0 < 0 or x0 < 0 or (j1 + j2 + j4 + j5) % 2:
            continue
        if not (adm(r, j1, j5, q0) and adm(r, j4, j2, q0)):
            continue
        n = (j4 + j5 - x0) // 2
        xs = [x for x in range(x0, j4 + j5 + 1, 2) if adm(r, j1, j2, x) and adm(r, j4, j5, x)]
        if len(xs) == n + 1 and xs[0] == x0 and n >= 1:
            yield j1, j2, j4, j5, q0, x0, n, xs


def main():
    worst_ratio = worst_sum = worst_prod = 0.0
    control_spread = 0.0
    count = 0
    for r in (5, 7, 9):
        omega, sj = make(r)
        Q = cmath.exp(2j * math.pi / r)
        for j1, j2, j4, j5, q0, x0, n, xs in cases(r):
            a = Q ** (x0 + 1)
            b = Q ** ((j1 + j2 + x0) // 2 + 2)
            c = Q ** ((x0 + j4 - j5) // 2 + 1)
            w = [omega(j1, j2, j4, j5, x) * sj(j1, j2, j4, j5, q0, x) ** 2 for x in xs]
            wt = omega(j1, j5, j4, j2, q0)
            try:
                rat = [w[k] / tj(Q, a, b, c, Q ** n, k) for k in range(n + 1)]
                rhs = (pk(a * Q, Q, n) * pk(a * Q / (b * c), Q, n)
                       / (pk(a * Q / b, Q, n) * pk(a * Q / c, Q, n)))
                bad = [w[k] / tj(Q, a, b * Q, c, Q ** n, k) for k in range(n + 1)]
            except ZeroDivisionError:
                continue
            count += 1
            worst_ratio = max(worst_ratio, max(abs(t - rat[0]) for t in rat) / abs(rat[0]))
            worst_sum = max(worst_sum, abs(wt * sum(w) - 1))
            worst_prod = max(worst_prod, abs(rat[0] * rhs * wt - 1))
            control_spread = max(control_spread, max(abs(t - bad[0]) for t in bad) / abs(bad[0]))
    print(f"cases {count}: max ratio spread {worst_ratio:.1e}, max |weight*sum - 1| {worst_sum:.1e}, "
          f"max |kappa*rhs*weight - 1| {worst_prod:.1e}; control (b -> bQ) spread {control_spread:.2f}")
    ok = (count > 100 and worst_ratio < TOL and worst_sum < TOL and worst_prod < TOL
          and control_spread > 1e-2)
    print("FAIL" if not ok else "OK")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
