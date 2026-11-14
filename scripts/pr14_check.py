"""Numerical check (not a proof) of the Ponzano-Regge 1-4 Pachner move with the weights used in
Lightlike/PonzanoRegge: edge (2j+1)(-1)^{2j}, triangle (-1)^{ja+jb+jc}, tetrahedron {6j}.

Configuration: tetrahedron ABCD versus the four tetrahedra ABCE, ABDE, ACDE, BCDE around a new
interior vertex E (new edges AE, BE, CE, DE; new triangles ABE, ACE, ADE, BCE, BDE, CDE).

Claimed identity (for every spin d on the new edge DE):

    sum_{a,b,c} w(a) w(b) w(c) w(d) * (6 new triangle signs) * {ABCE}{ABDE}{ACDE}{BCDE}
        = (2d+1)^2 * {ABCD}

with a, b, c the spins of AE, BE, CE. Summing d gives the divergent vertex factor sum_d (2d+1)^2.
Exact arithmetic (SymPy). Controls: `--wrong-factor` checks against (2d+1) instead of (2d+1)^2,
`--wrong-edge-sign` drops (-1)^{2j}; each must fail. Exit 0 when the identity holds; the default run
also runs both controls and exits 0 only if they fail. With a control flag, only that control runs
and the exit code is 1 when it fails, as it must.
"""
import functools, itertools, sys
from sympy import Rational, S
from sympy.physics.wigner import wigner_6j

def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b

@functools.lru_cache(maxsize=None)
def six_j(j1, j2, j3, j4, j5, j6):
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return S(0)
    return wigner_6j(j1, j2, j3, j4, j5, j6)

def tet6j(col, p, q, r, s):
    e = lambda u, v: col[frozenset((u, v))]
    return six_j(e(p, q), e(q, r), e(r, p), e(r, s), e(p, s), e(q, s))

def tri_sign(col, u, v, w):
    t = col[frozenset((u, v))] + col[frozenset((v, w))] + col[frozenset((u, w))]
    return (-1) ** int(t) if t == int(t) else 0

TOL = 1e-12

def edge_w(j, wrong_sign=False):
    return (2 * j + 1) * (1 if wrong_sign else (-1) ** int(2 * j))

def half_range(top):
    x = S(0)
    while x <= top:
        yield x
        x += Rational(1, 2)

def run(jmax2=2, dmax2=2, wrong_sign=False, wrong_factor=False):
    """Max |LHS-RHS| over all colourings; prints one line."""
    w = lambda j: edge_w(j, wrong_sign)
    spins = [Rational(k, 2) for k in range(jmax2 + 1)]
    old = ["AB", "AC", "AD", "BC", "BD", "CD"]
    maxerr, nontriv, total = 0, 0, 0
    for vals in itertools.product(spins, repeat=6):
        col = {frozenset(k): v for k, v in zip(old, vals)}
        rhs0 = tet6j(col, "A", "B", "C", "D")
        for d in [Rational(k, 2) for k in range(dmax2 + 1)]:
            col[frozenset("DE")] = d
            lhs = S(0)
            for a in half_range(col[frozenset("AD")] + d):
                col[frozenset("AE")] = a
                for b in half_range(col[frozenset("BD")] + d):
                    col[frozenset("BE")] = b
                    for c in half_range(col[frozenset("CD")] + d):
                        col[frozenset("CE")] = c
                        t = (tet6j(col, "A", "B", "C", "E") * tet6j(col, "A", "B", "D", "E")
                             * tet6j(col, "A", "C", "D", "E") * tet6j(col, "B", "C", "D", "E"))
                        if t == 0:
                            continue
                        lhs += (w(a) * w(b) * w(c) * w(d)
                                * tri_sign(col, "A", "B", "E") * tri_sign(col, "A", "C", "E")
                                * tri_sign(col, "A", "D", "E") * tri_sign(col, "B", "C", "E")
                                * tri_sign(col, "B", "D", "E") * tri_sign(col, "C", "D", "E") * t)
            factor = (2 * d + 1) if wrong_factor else (2 * d + 1) ** 2
            rhs = factor * rhs0
            total += 1
            if lhs != 0 or rhs != 0:
                nontriv += 1
            maxerr = max(maxerr, abs(float(lhs - rhs)))
    tag = "[WRONG factor] " if wrong_factor else "[WRONG edge sign] " if wrong_sign else ""
    print(f"{tag}old spins <= {Rational(jmax2, 2)}, d <= {Rational(dmax2, 2)}: {total} cases, "
          f"{nontriv} nontrivial, max |LHS-RHS| = {maxerr:.2e}")
    return maxerr if nontriv else float("inf")

def main() -> int:
    args = [int(a) for a in sys.argv[1:] if not a.startswith("--")]
    sign, factor = "--wrong-edge-sign" in sys.argv, "--wrong-factor" in sys.argv
    if sign or factor:
        return 0 if run(*args, wrong_sign=sign, wrong_factor=factor) < TOL else 1
    ok = run(*args) < TOL
    controls = [run(*args, wrong_sign=True), run(*args, wrong_factor=True)]
    caught = all(e >= TOL for e in controls)
    print("OK" if ok and caught else "FAIL: " + ("identity" if not ok else "a control was not detected"))
    return 0 if ok and caught else 1

if __name__ == "__main__":
    sys.exit(main())
