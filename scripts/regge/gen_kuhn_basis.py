"""Generate Lightlike/Regge/Conv3/KuhnBasis.lean from the exact computation in regge3d_g0_certificate.py.

The Lean file proves, for each of the six symmetric basis matrices B, the polynomial identity
(face polynomials P_i divide their numerators exactly, see the certificate), and then assembles the
identity for a general symmetric B by linearity. Usage: python3 scripts/regge/gen_kuhn_basis.py KuhnBasis.lean KuhnLinear.lean KuhnLinear2.lean KuhnStar.lean (in Lightlike/Regge/Conv3/)
"""
import sys
import sympy as sp
import regge3d_g0_certificate as G

gv = sorted(G.g.free_symbols, key=str)
NAMES = ['00', '01', '02', '11', '12', '22']

def lean(e, vs=gv):
    e = sp.expand(e)
    if e == 0:
        return '0'
    ts = []
    for mon, c in sp.Poly(e, *vs).terms():
        c = sp.Rational(c)
        cs = '(%d : ℝ)' % c.p if c.q == 1 else '(%d/%d : ℝ)' % (c.p, c.q)
        m = '*'.join(('%s^(%d:ℕ)' % (v, k) if k > 1 else str(v)) for v, k in zip(vs, mon) if k)
        ts.append(cs + ('*' + m if m else ''))
    return '(' + ' + '.join(ts).replace('+ -', '- ') + ')'

poly, nums = G.pieces()
Ps = list(nums)
gs = 'g00 g01 g02 g11 g12 g22'
hyps = ' '.join('(hP%d : %s ≠ 0)' % (i + 1, lean(P)) for i, P in enumerate(Ps))
Pl = [lean(P) for P in Ps]

def sub_of(idx):
    return {x: (1 if x == G.bs[idx] else 0) for x in G.bs}

out = ['import Mathlib', '', '/-!',
       '# The Kuhn star identity as a polynomial identity in the chart Gram matrix', '',
       'For the Gram matrix `g0` of a chart (entries `g00, …, g22`) and a symmetric matrix `B` (the',
       'second-order jet), the sum over the 36 incidences of the Kuhn triangulation, written over the six',
       'distinct face polynomials `P₁, …, P₆`, equals `det g0 * tr (adj g0 * B) / 2`. Each face polynomial',
       'divides its numerator exactly, so for each of the six symmetric basis matrices the identity is',
       'proved by exact polynomial division (`ring1`), and the general identity follows by linearity.',
       'The statements are elementary algebra, generated from an exact computer-algebra computation',
       '(`scripts/regge/gen_kuhn_basis.py`) that cross-checks them independently.', '',
       '## Main results', '',
       '* `kuhn_basis_ij`: the identity for the basis matrix `E_ij`.',
       '* `kuhn_star_identity`: the identity for a general symmetric `B`.', '-/', '']
for idx, nm in enumerate(NAMES):
    sub = sub_of(idx)
    Nl = [lean(nums[P].subs(sub)) for P in Ps]
    Ql = [lean(sp.quo(sp.Poly(sp.expand(nums[P].subs(sub)), *gv), sp.Poly(P, *gv)).as_expr()) for P in Ps]
    lhs = ' + '.join([lean(poly.subs(sub))] + ['%s / %s' % (Nl[k], Pl[k]) for k in range(6)])
    tgt = '%s * %s / 2' % (lean(G.detg), lean(G.rho.subs(sub)))
    out += [            '/-- The Kuhn star identity for the basis matrix `E_%s`: the sum over the incidences equals' % nm,
            '`det g0 * tr (adj g0 * E_%s) / 2`, by exact division of each numerator by its face polynomial. -/' % nm,
            'theorem kuhn_basis_%s (%s : ℝ) %s :' % (nm, gs, hyps), '    ' + lhs + ' =', '    ' + tgt + ' := by']
    out += ['  have q%d : %s / %s = %s := by' % (k + 1, Nl[k], Pl[k], Ql[k]) + '\n    rw [div_eq_iff hP%d]\n    ring1' % (k + 1) for k in range(6)]
    out += ['  rw [%s]' % ', '.join('q%d' % (k + 1) for k in range(6)), '  ring1', '']
# general B: assemble by linearity without expanding the 36 fractions
bv = list(G.bs)
def lin(e):
    return lean(e, gv + bv)
hargs = ' '.join('(hP%d : %s ≠ 0)' % (i + 1, Pl[i]) for i in range(6))
hcall = ' '.join('hP%d' % (k + 1) for k in range(6))
bsum = lambda terms: ' + '.join('%s * (%s)' % (str(bv[j]), terms[j]) for j in range(6))
Nij = [[lean(nums[P].subs(sub_of(j))) for P in Ps] for j in range(6)]
Yj = [lean(poly.subs(sub_of(j))) for j in range(6)]
Rj = [lean(G.rho.subs(sub_of(j))) for j in range(6)]
# abstract assembly lemma
out += ['/-- Linearity bookkeeping: if `y j + x 1 j + ... + x 6 j = D * r j / 2` for each of the six basis',
        'indices, then the same holds for the `b`-weighted combination. -/',
        'theorem kuhn_assemble (D b0 b1 b2 b3 b4 b5 r0 r1 r2 r3 r4 r5 y0 y1 y2 y3 y4 y5 : ℝ)']
xs = ['x%d%d' % (i, j) for i in range(1, 7) for j in range(6)]
out += ['    (%s : ℝ)' % ' '.join(xs)]
for j in range(6):
    out += ['    (h%d : y%d + %s = D * r%d / 2)' % (j, j, ' + '.join('x%d%d' % (i, j) for i in range(1, 7)), j)]
bn = ['b%d' % j for j in range(6)]
out += ['    : (%s) + %s =' % (' + '.join('%s * y%d' % (bn[j], j) for j in range(6)),
        ' + '.join('(%s)' % ' + '.join('%s * x%d%d' % (bn[j], i, j) for j in range(6)) for i in range(1, 7))),
        '    D * (%s) / 2 := by' % ' + '.join('%s * r%d' % (bn[j], j) for j in range(6)),
        '  linear_combination ' + ' + '.join('%s * h%d' % (bn[j], j) for j in range(6)), '']
SPLIT = len(out)
out += ['set_option maxHeartbeats 650000 in',
        'set_option maxRecDepth 100000 in',
        '/-- The Kuhn star identity for a general symmetric matrix `B` with entries `b00, …, b22`, by',
        'linearity in `B` from the six basis identities. -/',
        'theorem kuhn_star_identity (%s %s : ℝ) %s :' % (gs, ' '.join(map(str, bv)), hargs)]
lhsg = ' + '.join([lin(poly)] + ['%s / %s' % (lin(nums[Ps[k]]), Pl[k]) for k in range(6)])
out += ['    ' + lhsg + ' =', '    %s * %s / 2 := by' % (lean(G.detg), lin(G.rho))]
hdr = '(%s %s : ℝ)' % (gs, ' '.join(map(str, bv)))
def lem(name, doc, stmt):
    caps = {'kuhn_lin_num1': 500000, 'kuhn_lin_num5': 500000, 'kuhn_lin_num6': 450000}
    return ([('set_option maxHeartbeats %d in' % caps[name])] if name in caps else []) + ['set_option maxRecDepth 100000 in', '/-- %s -/' % doc, 'theorem %s %s :' % (name, hdr), '    ' + stmt + ' := by', '  ring1', '']
LEMS = []
LEMS += lem('kuhn_lin_poly', 'The polynomial part is linear in `B`.', '%s = %s' % (lin(poly), bsum(Yj)))
for k in range(6):
    LEMS += lem('kuhn_lin_num%d' % (k + 1), 'The fraction with face polynomial `P%d` is linear in `B`.' % (k + 1),
                '%s / %s = %s' % (lin(nums[Ps[k]]), Pl[k], bsum(['%s / %s' % (Nij[j][k], Pl[k]) for j in range(6)])))
LEMS += lem('kuhn_lin_rho', 'The trace term is linear in `B`.', '%s = %s' % (lin(G.rho), bsum(Rj)))
call = ' '.join(['g00 g01 g02 g11 g12 g22', ' '.join(map(str, bv))])
e = '(kuhn_lin_poly %s)' % call
for k in range(6):
    e = '(congrArg₂ (· + ·) %s (kuhn_lin_num%d %s))' % (e, k + 1, call)
out += ['  have e := ' + e]
out += ['  exact (e.trans (kuhn_assemble %s %s %s %s %s %s)).trans (congrArg (fun x => %s * x / 2) (kuhn_lin_rho %s).symm)' % (lean(G.detg), ' '.join(map(str, bv)),
        ' '.join('(%s)' % r for r in Rj), ' '.join('(%s)' % y for y in Yj),
        ' '.join('(%s / %s)' % (Nij[j][k], Pl[k]) for k in range(6) for j in range(6)),
        ' '.join('(kuhn_basis_%s %s %s)' % (NAMES[j], gs, hcall) for j in range(6)), lean(G.detg), call)]
out += ['']
head = out[:SPLIT]; star = out[SPLIT:]
def lin_file(name, blocks):
    return '\n'.join(['import Mathlib', '', '/-!', '# Linearity in the jet for the Kuhn star identity (%s)' % name, '',
        'Pieces of the identity of `KuhnBasis` (the polynomial part, the six fractions and the trace',
        'term) are linear in the symmetric matrix `B`; each is proved by `ring1`. -/', ''] + blocks) + '\n'
blk = []   # one block per lemma (each ends with an empty line)
cur = []
for l in LEMS:
    cur.append(l)
    if l == '':
        blk.append(cur); cur = []
assert len(blk) == 8
flat = lambda bs: [l for b in bs for l in b]
def wrap(t):
    i = t.index('-/\n') + 3
    return t[:i] + '\nnamespace Lightlike.Regge.Conv3\n' + t[i:].rstrip('\n') + '\n\nend Lightlike.Regge.Conv3\n'
if len(sys.argv) > 4:   # basis, two linearity modules, star
    open(sys.argv[1], 'w').write(wrap('\n'.join(head) + '\n'))
    open(sys.argv[2], 'w').write(wrap(lin_file('part one', flat(blk[:4]))))
    open(sys.argv[3], 'w').write(wrap(lin_file('part two', flat(blk[4:]))))
    open(sys.argv[4], 'w').write(wrap('\n'.join(['import Mathlib', 'import Lightlike.Regge.Conv3.KuhnBasis', 'import Lightlike.Regge.Conv3.KuhnLinear', 'import Lightlike.Regge.Conv3.KuhnLinear2', '', '/-!',
        '# Kuhn star identity for a general jet', '',
        'The identity of `KuhnBasis` for a general symmetric `B`, from the six basis identities by linearity. -/', ''] + star) + '\n'))
else:
    open(sys.argv[1], 'w').write('\n'.join(head + LEMS + star) + '\n')
print('written', sum(map(len, out)))
