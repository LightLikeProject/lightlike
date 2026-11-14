"""Cross-check for the wrong-Schwarzschild test (Lightlike/GR/Schwarzschild.lean,
Lightlike/Tests/Curvature.lean).

Uses the project's conventions (Lightlike/Spacetime/Curvature.lean):
  Γ^i_{jk} = ½ g^{il} (∂_j g_{lk} + ∂_k g_{lj} − ∂_l g_{jk})
  R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ}Γ^λ_{νσ} − Γ^ρ_{νλ}Γ^λ_{μσ}
  R_{σν} = R^ρ_{σρν}

Checks:
  1. Schwarzschild diag(−f, 1/f, r², r² sin²θ), f = 1 − 2M/r, is Ricci-flat (control).
  2. The wrong metric with g_rr = f (power +1 instead of −1) is NOT Ricci-flat, and prints its
     Christoffel symbols, their r/θ-derivatives and its Ricci tensor (the formulas the Lean test
     proves).
Run: python3 scripts/wrong_schwarzschild_check.py
"""
import sympy as sp

t, r, th, ph, M = sp.symbols("t r theta phi M", real=True)
X = [t, r, th, ph]
f = 1 - 2 * M / r


def curvature(diag):
    g = sp.diag(*diag)
    gi = g.inv()
    n = 4
    G = [[[sp.simplify(sp.Rational(1, 2) * sum(
        gi[i, l] * (sp.diff(g[l, k], X[j]) + sp.diff(g[l, j], X[k]) - sp.diff(g[j, k], X[l]))
        for l in range(n))) for k in range(n)] for j in range(n)] for i in range(n)]

    def riem(p, s, m, v):
        return (sp.diff(G[p][v][s], X[m]) - sp.diff(G[p][m][s], X[v]) +
                sum(G[p][m][l] * G[l][v][s] - G[p][v][l] * G[l][m][s] for l in range(n)))

    Ric = sp.Matrix(n, n, lambda s, v: sp.simplify(sum(riem(p, s, p, v) for p in range(n))))
    return G, Ric


_, Ric_s = curvature([-f, 1 / f, r**2, r**2 * sp.sin(th)**2])
assert Ric_s == sp.zeros(4, 4), Ric_s
print("Schwarzschild: Ricci = 0 (control passes)")

G_w, Ric_w = curvature([-f, f, r**2, r**2 * sp.sin(th)**2])
print("\nWrong metric g_rr = 1 - 2M/r. Nonzero Christoffels Γ^i_jk (j <= k):")
for i in range(4):
    for j in range(4):
        for k in range(j, 4):
            if G_w[i][j][k] != 0:
                print(f"  Γ^{i}_{j}{k} = {sp.factor(G_w[i][j][k])}")
print("\nRicci tensor (nonzero components):")
for s in range(4):
    for v in range(4):
        if Ric_w[s, v] != 0:
            print(f"  R_{s}{v} = {sp.factor(Ric_w[s, v])}")
assert Ric_w != sp.zeros(4, 4)
R22 = sp.factor(Ric_w[2, 2])
print("\nR_θθ =", R22, "; at M = 1, r = 3:", R22.subs({M: 1, r: 3}))
assert R22.subs({M: 1, r: 3}) != 0
print("Wrong metric is NOT Ricci-flat (as the Lean test proves).")
