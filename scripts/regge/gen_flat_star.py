"""Exact data for the dg = 0 star identity (Lightlike/Regge/Conv3/FlatStar.lean).

At a point where the first derivatives of the metric vanish, the squared lengths of the 36
incidences of the Kuhn triangulation are q_ab = D.G D (Gram part) and r_ab = (1/2) D.dd(s,s).D +
(1/24) D.dd(D,D).D (second-order part, linear in the second derivatives dd), with D the edge vector
and s the midpoint offset.  This module computes, with exact polynomial arithmetic over Q, the
polynomials of the identity
    sum_i E_i = (R det / 2),   E_i = N'_i - N_i/2 (P1'_i/P1_i + P2'_i/P2_i),
and checks that the six distinct face polynomials divide their numerators.
"""
import itertools
from sympy import QQ, Rational as Q
from sympy.polys.rings import ring

NAMES_G = ['g00', 'g01', 'g02', 'g11', 'g12', 'g22']
PAIRS = [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]
NAMES_D = ['d%d%d_%d%d' % (k, l, i, j) for (k, l) in PAIRS for (i, j) in PAIRS]
Rg, *gens = ring(NAMES_G + NAMES_D, QQ)
g = dict(zip(PAIRS, gens[:6]))
dd = {}
for n, ((k, l), (i, j)) in enumerate(itertools.product(PAIRS, PAIRS)):
    dd[(k, l, i, j)] = gens[6 + n]
def G(i, j): return g[(min(i, j), max(i, j))]
def DD(k, l, i, j): return dd[(min(k, l), max(k, l), min(i, j), max(i, j))]
def Gq(a, b): return sum((G(i, j) * a[i] * b[j] for i in range(3) for j in range(3)), Rg(0))
def Dq(s, t, D):   # D . ddmat(s,t) . D
    return sum((s[k] * t[l] * DD(k, l, i, j) * D[i] * D[j]
                for k in range(3) for l in range(3) for i in range(3) for j in range(3)), Rg(0))

kv = [(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)]
perms = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
hP = [0, 0, 0, 1, 1, 2]; hQ = [1, 2, 3, 2, 3, 3]; hR = [2, 1, 1, 0, 0, 0]; hS = [3, 3, 2, 3, 2, 1]
def kpos(s, h, k):
    return [Q(kv[k][perms[s][i]]) - Q(kv[hP[h]][perms[s][i]] + kv[hQ[h]][perms[s][i]], 2) for i in range(3)]

def lengths(s_, h):
    p = [kpos(s_, h, k) for k in range(4)]
    def e(a, b):
        mid = [(p[a][i] + p[b][i]) / 2 for i in range(3)]
        D = [p[b][i] - p[a][i] for i in range(3)]
        return Gq(D, D), Dq(mid, mid, D) / 2 + Dq(D, D, D) / 24
    es = [e(hP[h], hQ[h]), e(hP[h], hR[h]), e(hQ[h], hR[h]), e(hP[h], hS[h]), e(hQ[h], hS[h]), e(hR[h], hS[h])]
    return [x[0] for x in es], [x[1] for x in es]

def PPoly(a, b, c): return a * b - (b + a - c) ** 2 / 4
def NPoly(a, b, c, d, e, f): return a * (b + d - f) / 2 - (b + a - c) * (d + a - e) / 4
def PPoly1(a, b, c, a1, b1, c1): return a1 * b + a * b1 - (b + a - c) * (b1 + a1 - c1) / 2
def NPoly1(a, b, c, d, e, f, a1, b1, c1, d1, e1, f1):
    return a1 * (b + d - f) / 2 + a * (b1 + d1 - f1) / 2 - ((b1 + a1 - c1) * (d + a - e) + (b + a - c) * (d1 + a1 - e1)) / 4

def data():
    inc = []
    for s_ in range(6):
        for h in range(6):
            q, r = lengths(s_, h)
            P1 = PPoly(q[0], q[1], q[2]); P2 = PPoly(q[0], q[3], q[4])
            N = NPoly(*q); Np = NPoly1(*q, *r)
            P1p = PPoly1(q[0], q[1], q[2], r[0], r[1], r[2]); P2p = PPoly1(q[0], q[3], q[4], r[0], r[3], r[4])
            inc.append(dict(s=s_, h=h, q=q, r=r, P1=P1, P2=P2, N=N, Np=Np, P1p=P1p, P2p=P2p))
    return inc

def _unused():
    inc = data()
    Ps = []
    for x in inc:
        for P in (x['P1'], x['P2']):
            if not any(P == Pk or P == -Pk for Pk in Ps):
                Ps.append(P)
    print('distinct face polynomials (up to sign):', len(Ps))
    poly = sum((x['Np'] for x in inc), Rg(0))
    X = [Rg(0)] * len(Ps)
    for x in inc:
        for P, Pp in ((x['P1'], x['P1p']), (x['P2'], x['P2p'])):
            for k, Pk in enumerate(Ps):
                if P == Pk: X[k] += -x['N'] * Pp / 2; break
                if P == -Pk: X[k] += x['N'] * Pp / 2; break
    for k, Pk in enumerate(Ps):
        qt, rem = X[k].div(Pk)
        print(k, 'quotient terms', len(qt) if not isinstance(qt, list) else len(qt[0]), 'remainder zero:', rem == 0)

def adjugate():
    M = [[G(i, j) for j in range(3)] for i in range(3)]
    def cof(i, j):
        r = [x for x in range(3) if x != i]; c = [x for x in range(3) if x != j]
        m = M[r[0]][c[0]] * M[r[1]][c[1]] - M[r[0]][c[1]] * M[r[1]][c[0]]
        return m if (i + j) % 2 == 0 else -m
    return [[cof(j, i) for j in range(3)] for i in range(3)]

def det_poly():
    M = [[G(i, j) for j in range(3)] for i in range(3)]
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

def rhs_num():
    """(1/4) sum adj_{s n} adj_{r l} [ DD(n,r,l,s)+DD(s,r,l,n)-DD(l,r,n,s) - DD(r,n,l,s)-DD(s,n,l,r)+DD(l,n,r,s) ]"""
    A = adjugate(); tot = Rg(0)
    for s in range(3):
        for n in range(3):
            for r in range(3):
                for l in range(3):
                    br = (DD(n, r, l, s) + DD(s, r, l, n) - DD(l, r, n, s)
                          - DD(r, n, l, s) - DD(s, n, l, r) + DD(l, n, r, s))
                    tot += A[s][n] * A[r][l] * br
    return tot / 4

def check():
    inc = data()
    Ps = []
    for x in inc:
        for P in (x['P1'], x['P2']):
            if not any(P == Pk or P == -Pk for Pk in Ps): Ps.append(P)
    poly = sum((x['Np'] for x in inc), Rg(0))
    X = [Rg(0)] * len(Ps)
    for x in inc:
        for P, Pp in ((x['P1'], x['P1p']), (x['P2'], x['P2p'])):
            for k, Pk in enumerate(Ps):
                if P == Pk: X[k] += -x['N'] * Pp / 2; break
                if P == -Pk: X[k] += x['N'] * Pp / 2; break
    Qs = [X[k].div(Ps[k])[0] for k in range(len(Ps))]
    lhs = (poly + sum(Qs, Rg(0))) * det_poly()
    return lhs - rhs_num() == 0



def atom_G(i, j): return 'G %d %d' % (min(i, j), max(i, j))

def lean_poly(p):
    """Lean text of a polynomial of Rg with atoms G i j and dd k l i j."""
    names = []
    for n in NAMES_G:
        names.append('G %s %s' % (n[1], n[2]))
    for n in NAMES_D:
        k, l = n[1], n[2]; i, j = n[4], n[5]
        names.append('dd %s %s %s %s' % (k, l, i, j))
    terms = []
    for mon, c in p.terms():
        c = Q(c.numerator, c.denominator) if hasattr(c, 'numerator') else Q(c)
        cs = '(%d : ℝ)' % c.p if c.q == 1 else '(%d/%d : ℝ)' % (c.p, c.q)
        m = ' * '.join(('(%s)^%d' % (names[v], e) if e > 1 else '(%s)' % names[v]) for v, e in enumerate(mon) if e)
        terms.append(cs + (' * ' + m if m else ''))
    return '(' + ' + '.join(terms).replace('+ (-', '+ (-') + ')' if terms else '(0 : ℝ)'

def vec3(t):
    return '![%s]' % ', '.join('(%s : ℝ)' % ('%d/%d' % (Q(x).p, Q(x).q) if Q(x).q != 1 else '%d' % Q(x).p) for x in t)

def inc_text(s_, h):
    p = [kpos(s_, h, k) for k in range(4)]
    pairs = [(hP[h], hQ[h]), (hP[h], hR[h]), (hQ[h], hR[h]), (hP[h], hS[h]), (hQ[h], hS[h]), (hR[h], hS[h])]
    qs = []; rs = []
    for (a, b) in pairs:
        mid = [(p[a][i] + p[b][i]) / 2 for i in range(3)]
        D = [p[b][i] - p[a][i] for i in range(3)]
        qs.append('qf G %s' % vec3(D)); rs.append('rf dd %s %s' % (vec3(mid), vec3(D)))
    return 'Einc ![%s] ![%s]' % (', '.join(qs), ', '.join(rs))

def emit_lean():
    inc = data()
    Ps = []
    for x in inc:
        for P in (x['P1'], x['P2']):
            if not any(P == Pk for Pk in Ps): Ps.append(P)
    poly = sum((x['Np'] for x in inc), Rg(0))
    X = [Rg(0)] * len(Ps)
    for x in inc:
        for P, Pp in ((x['P1'], x['P1p']), (x['P2'], x['P2p'])):
            k = [i for i, Pk in enumerate(Ps) if P == Pk][0]
            X[k] += -x['N'] * Pp / 2
    Qs = [X[k].div(Ps[k])[0] for k in range(len(Ps))]
    det = det_poly()
    hyps = ' '.join('(hP%d : %s ≠ 0)' % (k + 1, lean_poly(P)) for k, P in enumerate(Ps))
    lhs = '∑ σ : Fin 6, ∑ h : Fin 6, Einc (lenQ G σ h) (lenR dd σ h)'
    out = ['theorem flat_star_identity (G : Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)',
           '    (hG : ∀ i j, G i j = G j i) (hd1 : ∀ k l i j, dd k l i j = dd l k i j)',
           '    (hd2 : ∀ k l i j, dd k l i j = dd k l j i)',
           '    %s' % hyps,
           '    (hdet : (Matrix.of G).det ≠ 0) :',
           '    ' + lhs.replace('\\n', '\n') + ' =',
           '    Rnum G dd / (Matrix.of G).det := by']
    for k, P in enumerate(Ps):
        out.append('  have hu%d : %s * (%s)⁻¹ = 1 := mul_inv_cancel₀ hP%d' % (k + 1, lean_poly(P), lean_poly(P), k + 1))
    out.append('  have hdetp : %s = (Matrix.of G).det := by' % lean_poly(det))
    out.append('    rw [Matrix.det_fin_three]')
    out.append('    simp only [Matrix.of_apply]')
    out.append('    rw [hG 1 0, hG 2 0, hG 2 1]')
    out.append('    ring')
    out.append('  rw [eq_div_iff hdet, ← hdetp]')
    out.append('  simp only [Rnum, Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,')
    out.append('    Matrix.cons_val, Fin.sum_univ_three]')
    lem_names = ', '.join('lenQ_%d_%d, lenR_%d_%d' % (a, b, a, b) for a in range(6) for b in range(6))
    out.append("  simp (config := { maxSteps := 100000000 }) only [Fin.sum_univ_six, %s, Einc, NPoly, NPoly', PPoly," % lem_names)
    out.append("    PPoly', qf, rf, ddq, Fin.sum_univ_three, Matrix.cons_val_zero,")
    out.append("    Matrix.cons_val_one, Matrix.cons_val, div_eq_mul_inv]")
    out.append('  rw [hG 1 0, hG 2 0, hG 2 1]')
    out.append('  simp only [hd1 1 0, hd1 2 0, hd1 2 1, hd2 _ _ 1 0, hd2 _ _ 2 0, hd2 _ _ 2 1]')
    comb = ' + '.join('(%s * %s) * hu%d' % (lean_poly(det), lean_poly(Qs[k]), k + 1) for k in range(len(Ps)))
    out.append('  linear_combination ' + comb)
    return '\n'.join(out)

def emit_lemmas():
    out = []
    for s_ in range(6):
        for h in range(6):
            p = [kpos(s_, h, k) for k in range(4)]
            pairs = [(hP[h], hQ[h]), (hP[h], hR[h]), (hQ[h], hR[h]), (hP[h], hS[h]), (hQ[h], hS[h]), (hR[h], hS[h])]
            qs = []; rs = []
            for (a, b) in pairs:
                mid = [(p[a][i] + p[b][i]) / 2 for i in range(3)]
                D = [p[b][i] - p[a][i] for i in range(3)]
                qs.append('qf G %s' % vec3(D)); rs.append('rf dd %s %s' % (vec3(mid), vec3(D)))
            tac = ('  ext i\n  fin_cases i <;> simp [%s, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>\n'
                   '    fin_cases j <;> simp <;> norm_num')
            out.append('/-- The Gram squared lengths of the incidence `(%d, %d)` with explicit edge vectors. -/\n'
                       'theorem lenQ_%d_%d (G : Fin 3 → Fin 3 → ℝ) : lenQ G %d %d = ![%s] := by\n%s\n'
                       % (s_, h, s_, h, s_, h, ', '.join(qs), tac.replace(' <;> norm_num', '') % 'lenQ'))
            out.append('/-- The second-order lengths of the incidence `(%d, %d)` with explicit edge data. -/\n'
                       'theorem lenR_%d_%d (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd %d %d = ![%s] := by\n%s\n'
                       % (s_, h, s_, h, s_, h, ', '.join(rs), tac % 'lenR'))
    return '\n'.join(out)

if __name__ == '__main__':
    import sys
    if len(sys.argv) > 1:
        open(sys.argv[1], 'w').write(emit_lemmas() + '\n' + emit_lean() + '\n')
    else:
        print('identity (Poly + sum Q) det = RHS:', check())
