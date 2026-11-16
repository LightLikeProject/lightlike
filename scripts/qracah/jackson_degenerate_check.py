"""Numerical check of the degenerate case of Jackson's sum, b = a q^(n+1) (stdlib only).

With pk(z, q, k) = (z; q)_k, checks for seeded random complex q, a, c and n <= 6 that

* the term tDeg = (1 - a q^(2k))/(1 - a) * (a, c; q)_k / (q, aq/c; q)_k * c^-k equals Jackson's term
  Tj at b = a q^(n+1), x = q^n, for k <= n;
* sDeg(n) = (aq, cq; q)_n / ((q, aq/c; q)_n c^n) satisfies sDeg(n) - sDeg(n-1) = tDeg(n);
* sDeg(n) equals the sum of tDeg over k <= n, and Jackson's right side (aq, aq/(bc); q)_n /
  (aq/b, aq/c; q)_n at b = a q^(n+1).

Control: with c replaced by 1.5 c in the closed form the sum does not match. Exit code 1 on failure.
"""
import random
import sys

TOL = 1e-8


def pk(z, q, k):
    p = 1
    for i in range(k):
        p *= 1 - z * q ** i
    return p


def t_deg(q, a, c, k):
    return ((1 - a * q ** (2 * k)) / (1 - a) * pk(a, q, k) * pk(c, q, k)
            / (pk(q, q, k) * pk(a * q / c, q, k)) * (1 / c) ** k)


def s_deg(q, a, c, n):
    return pk(a * q, q, n) * pk(c * q, q, n) / (pk(q, q, n) * pk(a * q / c, q, n) * c ** n)


def tj(q, a, b, c, x, k):
    return ((1 - a * q ** (2 * k)) / (1 - a)
            * (pk(a, q, k) * pk(b, q, k) * pk(c, q, k) * pk(1 / x, q, k))
            / (pk(q, q, k) * pk(a * q / b, q, k) * pk(a * q / c, q, k) * pk(a * q * x, q, k))
            * (a * q * x / (b * c)) ** k)


def main():
    random.seed(314159)
    e_term = e_tel = e_sum = e_rhs = e_ctl = 0.0
    for _ in range(200):
        q = complex(random.uniform(.3, 1.3), random.uniform(-.8, .8))
        a = complex(random.uniform(.2, 2), random.uniform(-1, 1))
        c = complex(random.uniform(.2, 2), random.uniform(-1, 1))
        n = random.randint(1, 6)
        b = a * q ** (n + 1)
        e_term = max(e_term, max(abs(tj(q, a, b, c, q ** n, k) - t_deg(q, a, c, k)) for k in range(n + 1)))
        e_tel = max(e_tel, abs(s_deg(q, a, c, n) - s_deg(q, a, c, n - 1) - t_deg(q, a, c, n))
                    / abs(t_deg(q, a, c, n)))
        total = sum(t_deg(q, a, c, k) for k in range(n + 1))
        e_sum = max(e_sum, abs(total - s_deg(q, a, c, n)) / abs(total))
        rhs = pk(a * q, q, n) * pk(a * q / (b * c), q, n) / (pk(a * q / b, q, n) * pk(a * q / c, q, n))
        e_rhs = max(e_rhs, abs(total - rhs) / abs(total))
        e_ctl = max(e_ctl, abs(total - s_deg(q, a, 1.5 * c, n)) / abs(total))
    print(f"term vs Tj {e_term:.1e}, telescoping {e_tel:.1e}, sum vs closed form {e_sum:.1e}, "
          f"sum vs Jackson right side {e_rhs:.1e}; control (c -> 1.5c) {e_ctl:.2f}")
    ok = e_term < TOL and e_tel < TOL and e_sum < TOL and e_rhs < TOL and e_ctl > 1e-2
    print("OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
