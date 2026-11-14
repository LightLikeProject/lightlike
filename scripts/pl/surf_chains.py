"""The finite chains of 2D moves used in the classification of surfaces (milestone PL3), verified
with the Python replica of the Lean checker (check_chain.py) and printed as Lean data.

The move lists were found with a bidirectional search over complexes up to isomorphism rel boundary
(ss-format moves, labels ('p', n) for the labels of a piece and ('n', k) for new vertices).  This
script relabels them to natural numbers, composes them, checks every chain with the exact
acceptance conditions of `checkChain` and prints `B`, `S`, `X`, the moves and the result `Y`.

Usage: python3 scripts/pl/surf_chains.py [name ...]   (no name: check all, run the wrong-input
controls and print a summary)
"""
import itertools
import pathlib
import sys

# `check_chain` sits next to this script; `python3 -I` drops the script directory from the path.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from check_chain import (F, ChainError, check, from_ss, inverse, lean_B, lean_K, lean_ms,  # noqa: E402
                         lean_S, relabel, rename_moves, verts)

P6 = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 1, 5), (1, 2, 4), (2, 3, 5), (1, 3, 4),
      (2, 4, 5), (1, 3, 5)]
T9 = [(0, 1, 2), (0, 1, 7), (0, 2, 5), (0, 3, 5), (0, 3, 6), (0, 6, 7), (1, 2, 4), (1, 3, 4),
      (1, 3, 8), (1, 7, 8), (2, 4, 6), (2, 5, 8), (2, 6, 8), (3, 4, 5), (3, 6, 8), (4, 5, 7),
      (4, 6, 7), (5, 7, 8)]


def K_of(ts):
    return F(F(t) for t in ts)


def erase(K, t):
    return K - {F(t)}


def mapK(K, m):
    return F(F(m[u] for u in t) for t in K)


def lab(u, new_base):
    """ss labels to naturals: ('p', n) -> n, ('n', k) -> new_base + k, integers unchanged."""
    if isinstance(u, tuple):
        return u[1] if u[0] == 'p' else new_base + u[1]
    return u


def ss_to_nat(path, new_base):
    ms = from_ss(path)
    return [(k,) + tuple(lab(u, new_base) for u in mv) for (k, *mv) in ms]


def find_map(K, P, fixed):
    """A relabelling m of the labels of P with m = fixed on the keys of `fixed` and K = P.map m."""
    src = sorted(verts(P) - set(fixed))
    dst = sorted(verts(K) - set(fixed.values()))
    if len(src) != len(dst):
        return None
    for perm in itertools.permutations(dst):
        m = dict(fixed)
        m.update(zip(src, perm))
        if mapK(P, m) == K:
            return m
    return None


def rename_all(B, S, K, targets):
    """Moves renaming each vertex u to targets[u], one after the other (targets fresh)."""
    ms = []
    for u, u2 in targets.items():
        if u == u2:
            continue
        m, K2 = rename_moves(K, u, u2, B)
        assert check(B, S, K, m) == K2
        ms += m
        K = K2
    return ms, K


# ---------------------------------------------------------------------------------------------
# Piece slides: the piece glued at 012 moves to the adjacent triangle {1, 2, z}, with all its
# interior vertices replaced by new ones.  X = {1,2,z} + (P - 012), Y = {012} + (P - 012).map b,
# b = (0, 1, 2 -> 1, 2, z; n -> n + shift).  B = {0, 1, 2, z}, S = [(1, 2)].

SLIDE_SS = {
    'P6': [('flip', (1, 2), (('p', 4), 6)), ('flip', (('p', 4), 2), (('p', 5), 6)),
           ('flip', (('p', 3), 0), (('p', 4), 2)), ('flip', (2, ('p', 5)), (('p', 3), 6)),
           ('flip', (('p', 4), 0), (('p', 5), 2)), ('flip', (('p', 5), 0), (1, 2))],
    'T9': [('flip', (1, 2), (9, ('p', 4))), ('flip', (('p', 4), 1), (('p', 3), 9)),
           ('flip', (('p', 3), 1), (('p', 8), 9)), ('flip', (('p', 8), 1), (9, ('p', 7))),
           ('flip', (('p', 7), 0), (('p', 6), 1)), ('flip', (0, ('p', 6)), (('p', 3), 1)),
           ('flip', (0, ('p', 3)), (('p', 5), 1)), ('flip', (0, ('p', 5)), (1, 2))],
}
SLIDE_Z = {'P6': 6, 'T9': 9}
SLIDE_SHIFT = {'P6': 4, 'T9': 7}


def slide_chain(name):
    P = K_of(P6 if name == 'P6' else T9)
    z, shift = SLIDE_Z[name], SLIDE_SHIFT[name]
    B, S = {0, 1, 2, z}, [(1, 2)]
    X = erase(P, (0, 1, 2)) | {F({1, 2, z})}
    ms = ss_to_nat(SLIDE_SS[name], 100)
    K = check(B, S, X, ms)
    m = find_map(erase(K, (0, 1, 2)), erase(P, (0, 1, 2)), {0: 1, 1: 2, 2: z})
    assert m is not None
    targets = {m[n]: n + shift for n in sorted(verts(P)) if n > 2}
    ms2, K2 = rename_all(B, S, K, targets)
    ms += ms2
    b = {0: 1, 1: 2, 2: z}
    b.update({n: n + shift for n in verts(P) if n > 2})
    Y = mapK(erase(P, (0, 1, 2)), b) | {F({0, 1, 2})}
    assert check(B, S, X, ms) == Y
    return dict(B=B, S=S, X=X, ms=ms, Y=Y)


# ---------------------------------------------------------------------------------------------
# Helpers for the handle chains.  tube(x, y) is the annulus between the ordered triangles x and y.


def tube(x, y):
    (a, b, c), (p, q, r) = x, y
    return K_of([(a, b, p), (b, p, q), (b, c, q), (c, q, r), (c, a, r), (a, r, p)])


def tab(l, s):
    """The label map of `tabE l s` in Lean: n -> l[n] for n < len(l), n -> n + s otherwise."""
    return lambda n: l[n] if n < len(l) else n + s


def mapF(K, f):
    return F(F(f(u) for u in t) for t in K)


P6K, T9K = K_of(P6), K_of(T9)
G134 = tab([1, 3, 4], 3)
# The Klein bottle piece: a second P6 glued to P6 at 134 (labels 0..8).
KB = erase(P6K, (1, 3, 4)) | mapF(erase(P6K, (0, 1, 2)), G134)
E012 = lambda K: erase(K, (0, 1, 2))


# The layer chain: a tube between 012 and 345 gets two more rings, 678 and (9, 10, 11).
LAYER_MS = [('sub', 1, 2, 4, 7), ('sub', 0, 1, 3, 6), ('sub', 2, 4, 5, 8), ('flip', 1, 4, 7, 3),
            ('flip', 0, 3, 5, 6), ('flip', 2, 5, 8, 0), ('flip', 1, 3, 6, 7), ('flip', 4, 2, 7, 8),
            ('flip', 0, 5, 6, 8), ('sub', 7, 8, 4, 10), ('sub', 6, 7, 3, 9), ('sub', 8, 4, 5, 11),
            ('flip', 7, 4, 10, 3), ('flip', 6, 3, 5, 9), ('flip', 8, 5, 11, 6), ('flip', 7, 3, 9, 10),
            ('flip', 4, 8, 10, 11), ('flip', 6, 5, 9, 11)]


def layer_chain():
    B = set(range(6))
    S = [(x, y) for x in (0, 1, 2) for y in (3, 4, 5)]
    X = tube((0, 1, 2), (3, 4, 5))
    Y = tube((0, 1, 2), (6, 7, 8)) | tube((6, 7, 8), (9, 10, 11)) | tube((9, 10, 11), (3, 4, 5))
    assert check(B, S, X, LAYER_MS) == Y
    return dict(B=B, S=S, X=X, ms=LAYER_MS, Y=Y)


# The tube slide: the end pqr = 345 of the tube from abc = 012 moves across the triangle qrs = 456.
def tslide_chain():
    B = set(range(7))
    S = [(4, 5)] + [(x, y) for x in (0, 1, 2) for y in (3, 4, 5, 6)]
    X = tube((0, 1, 2), (3, 4, 5)) | {F({4, 5, 6})}
    ms = [('flip', 4, 5, 2, 6), ('flip', 1, 3, 0, 4), ('flip', 4, 2, 1, 6), ('flip', 0, 3, 4, 5)]
    Y = {F({3, 4, 5})} | tube((0, 1, 2), (4, 6, 5))
    assert check(B, S, X, ms) == Y
    return dict(B=B, S=S, X=X, ms=ms, Y=Y)


# The final chains: a two-ring tube from 012 to the triangle 019 (adjacent along 01), entering in
# the order o, becomes a torus (o a rotation of (0, 1, 9)) or a Klein bottle (o reversed) glued at
# 012, with 019 restored.  The result is the piece with its interior labels permuted by `perm`.
FINAL_MS = {
    (0, 1, 9): [('flip', 3, 6, 8, 4), ('flip', 6, 9, 0, 8), ('flip', 0, 1, 7, 3), ('flip', 8, 9, 0, 1),
                ('flip', 4, 5, 2, 7), ('flip', 8, 3, 4, 5), ('flip', 7, 0, 3, 6), ('flip', 4, 7, 2, 6)],
    (1, 9, 0): [('flip', 3, 6, 8, 4), ('flip', 6, 8, 4, 0), ('flip', 0, 1, 6, 3), ('flip', 0, 3, 5, 6),
                ('flip', 4, 5, 2, 7), ('flip', 9, 7, 1, 8), ('flip', 9, 8, 0, 1), ('flip', 4, 1, 2, 3)],
    (9, 0, 1): [('flip', 3, 8, 6, 5), ('flip', 0, 1, 8, 3), ('flip', 6, 8, 5, 1), ('flip', 1, 3, 8, 4),
                ('flip', 7, 9, 0, 6), ('flip', 0, 5, 2, 3), ('flip', 9, 6, 0, 1), ('flip', 4, 5, 2, 7)],
    (0, 9, 1): [('flip', 3, 6, 8, 4), ('flip', 0, 1, 6, 3), ('flip', 0, 3, 5, 6), ('flip', 4, 5, 7, 2),
                ('flip', 7, 6, 0, 4), ('flip', 8, 9, 1, 7), ('flip', 9, 7, 0, 1), ('flip', 7, 8, 1, 5),
                ('flip', 0, 6, 5, 4)],
    (1, 0, 9): [('flip', 0, 1, 7, 3), ('flip', 5, 7, 4, 8), ('flip', 0, 3, 5, 7), ('flip', 4, 5, 8, 2),
                ('flip', 8, 7, 0, 4), ('flip', 6, 9, 1, 8), ('flip', 3, 8, 6, 5), ('flip', 9, 8, 0, 1),
                ('flip', 8, 6, 1, 5), ('flip', 0, 7, 5, 4)],
    (9, 1, 0): [('flip', 3, 6, 8, 4), ('flip', 0, 8, 1, 6), ('flip', 0, 1, 6, 3), ('flip', 0, 3, 5, 6),
                ('flip', 4, 5, 2, 7), ('flip', 6, 9, 0, 7), ('flip', 7, 6, 0, 4), ('flip', 9, 7, 0, 1),
                ('flip', 7, 8, 1, 5), ('flip', 0, 6, 5, 4)],
}
STRAIGHT = [(0, 1, 9), (1, 9, 0), (9, 0, 1)]
TWISTED = [(0, 9, 1), (1, 0, 9), (9, 1, 0)]


def final_X(o):
    return tube((0, 1, 2), (3, 4, 5)) | tube((3, 4, 5), (6, 7, 8)) | tube((6, 7, 8), o)


def final_chain(o):
    B, S = {0, 1, 2, 9}, [(0, 1)]
    X = final_X(o)
    K = check(B, S, X, FINAL_MS[o])
    P = T9K if o in STRAIGHT else KB
    m = find_map(K - {F({0, 1, 9})}, E012(P), {0: 0, 1: 1, 2: 2})
    assert m is not None
    perm = [m[n] for n in range(9)]
    Y = {F({0, 1, 9})} | mapF(E012(P), tab(perm, 0))
    assert K == Y
    return dict(B=B, S=S, X=X, ms=FINAL_MS[o], Y=Y, perm=perm)


# The cross-cap chain: the Moebius band of a one-sided cut becomes the fan with a projective plane
# glued at its triangle 320 (P6 labels 0, 1, 2 -> 3, 2, 0 and 3, 4, 5 -> 6, 7, 8).
BAND = K_of([(0, 3, 4), (0, 3, 5), (1, 4, 0), (1, 4, 5), (2, 5, 0), (2, 5, 4)])
CAP = K_of([(3, 4, 2), (3, 2, 0), (3, 0, 1), (3, 1, 5)])
CC_MS = [('sub', 2, 4, 5, 100), ('flip', 0, 5, 3, 2), ('sub', 0, 2, 3, 154), ('sub', 154, 0, 3, 460),
         ('flip', 1, 4, 0, 5), ('flip', 2, 5, 3, 100), ('flip', 4, 5, 0, 100), ('flip', 3, 0, 460, 4),
         ('flip', 100, 5, 0, 3), ('flip', 2, 3, 100, 154), ('flip', 4, 0, 100, 460),
         ('flip', 100, 4, 460, 2), ('flip', 5, 0, 1, 3), ('flip', 460, 4, 2, 3)]


def cc_chain():
    B = set(range(6))
    S = [(0, 3), (0, 4), (0, 5), (1, 4), (4, 5), (2, 5), (3, 2), (3, 1)]
    Y = erase(CAP, (3, 2, 0)) | mapF(E012(P6K), tab([3, 2, 0], 3))
    K = check(B, S, BAND, CC_MS)
    m = find_map(K, Y, {u: u for u in range(6)})
    assert m is not None
    ms = relabel(CC_MS, {v: k for k, v in m.items()})
    assert check(B, S, BAND, ms) == Y
    return dict(B=B, S=S, X=BAND, ms=ms, Y=Y)


# The Dyck chain: a torus glued to a projective plane equals two more projective planes, rel the
# boundary 012 of the projective plane.  Reverse a straight final chain (o = 019), slide the tube end
# once round a one-sided loop of the projective plane, then run the twisted final chain (o = 910).
SLIDE = lambda a, b, c, p, q, r, s: [('flip', q, r, c, s), ('flip', b, p, a, q), ('flip', q, c, b, s),
                                     ('flip', a, p, q, r)]
DYCK_STEPS = None  # computed by dyck_chain


def dyck_chain():
    from collections import deque
    region = [t for t in P6K if t not in (F({0, 1, 2}), F({1, 3, 4}))]

    def other(e, u, v):
        return [t for t in P6K if {u, v} <= t and t != F(e)][0]

    def nbrs(e):
        p, q, r = e
        out = []
        for (u, v, kind) in [(q, r, 0), (r, p, 1), (p, q, 2)]:
            rho = other(e, u, v)
            if rho not in region:
                continue
            s_ = next(iter(rho - {u, v}))
            out.append(([(q, s_, r), (p, r, s_), (s_, q, p)][kind], (kind, [(p, q, r, s_), (q, r, p, s_),
                                                                       (r, p, q, s_)][kind])))
        return out

    def raw_final(o):
        """The final chain relabelled so that its result is exactly 019 + (piece - 012)."""
        c = final_chain(o)
        inv = {v: k for k, v in enumerate(c['perm'])}
        inv[9] = 9
        return relabel(c['ms'], inv), tuple(inv[u] for u in (3, 4, 5)), tuple(inv[u] for u in (6, 7, 8))

    phi_s = {0: 1, 1: 3, 2: 4, 9: 5}
    o, ot = (0, 1, 9), (9, 1, 0)
    e0 = tuple(phi_s[u] for u in o)
    goal = tuple(phi_s[u] for u in ot)
    prev, dq = {e0: None}, deque([e0])
    while dq:
        e = dq.popleft()
        if e == goal:
            break
        for e2, mv in nbrs(e):
            if e2 not in prev:
                prev[e2] = (e, mv)
                dq.append(e2)
    steps, e = [], goal
    while prev[e]:
        steps.append(prev[e][1])
        e = prev[e][0]
    steps.reverse()
    ms_s, m1s, m2s = raw_final(o)
    ms_t, m1t, m2t = raw_final(ot)
    gam = {0: 1, 1: 3, 2: 4}
    for x, y in zip(m1s + m2s, m1t + m2t):
        gam[x] = y + 3
    phiS = dict(gam)
    phiS[9] = 5
    phiT = {0: 1, 1: 3, 2: 4, 9: 5}
    phiT.update({u: u + 3 for u in range(3, 9)})
    assert tuple(phiS[u] for u in m2s) == tuple(phiT[u] for u in m2t)
    ms = relabel(inverse(ms_s), phiS)
    a, b, c = (phiS[u] for u in m2s)
    for kind, (p, q, r, s_) in steps:
        ms += SLIDE(*[(a, b, c), (b, c, a), (c, a, b)][kind], p, q, r, s_)
    ms += relabel(ms_t, phiT)
    gamma = [gam[u] for u in range(9)]
    base = erase(E012(P6K), (1, 3, 4))
    X = base | mapF(E012(T9K), tab(gamma, 3))
    Y = base | mapF(E012(KB), G134)
    assert check({0, 1, 2}, [], X, ms) == Y
    return dict(B={0, 1, 2}, S=[], X=X, ms=ms, Y=Y, gamma=gamma)


def auts(P, k):
    """For each ordering (i, j, l) of 0, 1, 2: an automorphism of P extending 0, 1, 2 -> i, j, l."""
    out = {}
    for pi in itertools.permutations(range(3)):
        for rest in itertools.permutations(range(3, k)):
            a = list(pi) + list(rest)
            if mapF(P, tab(a, 0)) == P:
                out[pi] = a
                break
        assert pi in out
    return out


CHAINS = {'slideP6': lambda: slide_chain('P6'), 'slideT9': lambda: slide_chain('T9'),
          'layer': layer_chain, 'tslide': tslide_chain, 'cc': cc_chain, 'dyck': dyck_chain}
for _o in STRAIGHT + TWISTED:
    CHAINS['final%d%d%d' % _o] = (lambda o: lambda: final_chain(o))(_o)


def controls():
    """Wrong-input controls: the checker must reject corrupted chains. Every chain with its last
    move dropped misses its target, and the layer chain fails without its allowed new pairs."""
    n = 0
    for name, mk in CHAINS.items():
        c = mk()
        try:
            bad = check(c['B'], c['S'], c['X'], c['ms'][:-1])
        except ChainError:
            bad = None
        assert bad != c['Y'], f'{name}: dropping the last move still reaches the target'
        n += 1
    c = layer_chain()
    try:
        check(c['B'], [], c['X'], c['ms'])
    except ChainError:
        n += 1
    else:
        raise AssertionError('layer: accepted without its allowed pairs')
    return n


def show(name, c):
    print(f'-- {name}: {len(c["ms"])} moves, {len(c["X"])} -> {len(c["Y"])} triangles')
    for key in ('perm', 'gamma'):
        if key in c:
            print(key, ':=', c[key])
    print('B :=', lean_B(c['B']))
    print('S :=', lean_S(c['S']))
    print('X :=', lean_K(c['X']))
    print('Y :=', lean_K(c['Y']))
    print('ms :=', lean_ms(c['ms']))


if __name__ == '__main__':
    names = sys.argv[1:]
    if names == ['auts']:
        for nm, P, k in [('P6', P6K, 6), ('T9', T9K, 9)]:
            for pi, a in auts(P, k).items():
                print(nm, pi, a)
        sys.exit()
    for n, mk in CHAINS.items():
        c = mk()
        if not names:
            print(f'{n}: OK, {len(c["ms"])} moves')
        elif n in names:
            show(n, c)
    if not names:
        print(f'controls: OK, {controls()} corrupted chains rejected')
