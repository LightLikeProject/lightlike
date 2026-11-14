"""Numerical check (not a proof) of the Ponzano-Regge 2-3 Pachner move with the weights used in
Lightlike/PonzanoRegge: edge (2j+1)(-1)^{2j}, triangle (-1)^{ja+jb+jc}, tetrahedron {6j}.

Configuration: shared triangle ABC, apexes D, E. Two tetrahedra ABCD, ABCE (interior triangle ABC)
versus three tetrahedra ABDE, BCDE, CADE (interior edge DE, interior triangles ADE, BDE, CDE).
The 6j of a tetrahedron is taken directly from its geometry (triads = faces, columns = opposite
edges), independently of the Biedenharn-Elliott letter dictionary. Spins in {0, 1/2, ..., jmax}.
Exit 0 when the move holds; the default run also runs the control `--wrong-edge-sign` (drop
(-1)^{2j}) and exits 0 only if it fails. With the flag, only the control runs (exit 1, as it must).
"""
import itertools, sys
from sympy import Rational, S
from sympy.physics.wigner import wigner_6j

def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b

def six_j(j1, j2, j3, j4, j5, j6):
    # SymPy raises on inadmissible triads; the standard convention (and Physlib's) is 0
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return S(0)
    return wigner_6j(j1, j2, j3, j4, j5, j6)

def tet6j(col, p, q, r, s):
    # triangle pqr in the top row: {pq qr rp; rs ps qs}; columns pair opposite edges
    e = lambda u, v: col[frozenset((u, v))]
    return six_j(e(p, q), e(q, r), e(r, p), e(r, s), e(p, s), e(q, s))

def tri_sign(col, u, v, w):
    t = col[frozenset((u, v))] + col[frozenset((v, w))] + col[frozenset((u, w))]
    return (-1) ** int(t) if t == int(t) else 0  # half-integer perimeter: 6j vanish anyway

TOL = 1e-12

def edge_w(j, wrong=False):  # wrong: the control, drop (-1)^{2j}; the move must then fail
    return (2 * j + 1) * (1 if wrong else (-1) ** int(2 * j))

def run(jmax2=2, wrong=False):
    spins = [Rational(k, 2) for k in range(jmax2 + 1)]
    E9 = ["AB", "BC", "CA", "AD", "BD", "CD", "AE", "BE", "CE"]
    maxerr, nontriv, total = 0, 0, 0
    for vals in itertools.product(spins, repeat=9):
        col = {frozenset(k): v for k, v in zip(E9, vals)}
        lhs = tri_sign(col, "A", "B", "C") * tet6j(col, "A", "B", "C", "D") * tet6j(col, "A", "B", "C", "E")
        rhs = S(0)
        xmax = col[frozenset("AD")] + col[frozenset("AE")]
        x = S(0)
        while x <= xmax:
            col[frozenset("DE")] = x
            rhs += (edge_w(x, wrong) * tri_sign(col, "A", "D", "E") * tri_sign(col, "B", "D", "E")
                    * tri_sign(col, "C", "D", "E") * tet6j(col, "A", "B", "D", "E")
                    * tet6j(col, "B", "C", "D", "E") * tet6j(col, "C", "A", "D", "E"))
            x += Rational(1, 2)
        total += 1
        if lhs != 0 or rhs != 0:
            nontriv += 1
        maxerr = max(maxerr, abs(float(lhs - rhs)))
    print(f"{'[WRONG edge sign] ' if wrong else ''}spins <= {Rational(jmax2, 2)}: {total} colourings, {nontriv} nontrivial, max |LHS-RHS| = {maxerr:.2e}")
    return maxerr if nontriv else float("inf")

def main() -> int:
    args = [int(a) for a in sys.argv[1:] if not a.startswith("--")]
    if "--wrong-edge-sign" in sys.argv:
        return 0 if run(*args, wrong=True) < TOL else 1
    ok, caught = run(*args) < TOL, run(*args, wrong=True) >= TOL
    print("OK" if ok and caught else "FAIL: " + ("move" if not ok else "the control was not detected"))
    return 0 if ok and caught else 1

if __name__ == "__main__":
    sys.exit(main())
