"""Coverage of the nonvanishing hypotheses of Jackson's sum on the q-6j boundary evaluation (stdlib only).

For `x0 = j1 - j2 >= 0`, `q0 = j1 - j5 >= 0`, all admissible spins `0 <= j <= 2 (r - 2)` and
r = 4, ..., 11, with a = Q^(x0+1), b = Q^((j1+j2+x0)/2 + 2), c = Q^((x0+j4-j5)/2 + 1), n = (j4+j5-x0)/2
and Q = exp(2 pi i / r), a factor `1 - Q^m` vanishes exactly when r divides m. The script counts the
cases in which the old hypotheses `JHyp` (indices up to N + 2) and the sharper `JHypT` (indices up to
N, and n < N) of `Lightlike/TuraevViro/Reflect/JacksonWZ.lean` hold, and checks the recorded counts:
1206 cases, 296 under `JHyp`, 790 under `JHypT`, and that every case where `JHypT` fails has
j1 + j2 = j4 + j5.

Control: with the exponent of `b` shifted by one the counts change. Exit code 1 on failure.
"""
import itertools
import sys

EXPECTED = {"total": 1206, "JHyp": 296, "JHypT": 790, "T-fail degenerate": 416, "T-fail other": 0}


def adm(r, a, b, c):
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0 and a + b + c <= 2 * (r - 2)


def failures(r, ea, eb, ec, n, tight):
    nz = lambda e: e % r != 0
    f = set()
    if not nz(ea):
        f.add("1-a")
    top = n + 1 if tight else n + 3
    for i in range(top):
        if not nz(1 + i):
            f.add("1-q^(i+1)")
        if not nz(ea + 1 - eb + i):
            f.add("aq/b")
        if not nz(ea + 1 - ec + i):
            f.add("aq/c")
    for m in (range(n) if tight else range(n + 1)):
        for i in range(top):
            if not nz(ea + 1 + m + i):
                f.add("aq q^n q^i")
        if not nz(ea + 1 + m - eb) or not nz(ea + 1 + m - ec):
            f.add("aq q^n /b|c")
    return f


def count(shift_b):
    t = {k: 0 for k in EXPECTED}
    for r in range(4, 12):
        for j1, j2, j4, j5 in itertools.product(range(2 * (r - 2) + 1), repeat=4):
            q0, x0 = j1 - j5, j1 - j2
            if q0 < 0 or x0 < 0 or (j1 + j2 + j4 + j5) % 2:
                continue
            if not (adm(r, j1, j5, q0) and adm(r, j4, j2, q0)):
                continue
            n = (j4 + j5 - x0) // 2
            xs = [x for x in range(x0, j4 + j5 + 1, 2) if adm(r, j1, j2, x) and adm(r, j4, j5, x)]
            if not xs or xs[0] != x0 or len(xs) != n + 1:
                continue
            ea, eb, ec = x0 + 1, (j1 + j2 + x0) // 2 + 2 + shift_b, (x0 + j4 - j5) // 2 + 1
            old, new = failures(r, ea, eb, ec, n, False), failures(r, ea, eb, ec, n, True)
            t["total"] += 1
            t["JHyp"] += not old
            t["JHypT"] += not new
            if new:
                t["T-fail degenerate"] += j1 + j2 == j4 + j5
                t["T-fail other"] += j1 + j2 != j4 + j5
    return t


def main():
    got = count(0)
    print("counts", got)
    ok = got == EXPECTED
    control = count(1)
    print("control (exponent of b shifted by one)", control)
    ok = ok and control != EXPECTED
    print("OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
