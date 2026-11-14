"""Python replica of the move checker `checkChain` in Lightlike/Surfaces/Check.lean.

A complex is a set of frozensets of natural numbers.  `B` is the set of boundary labels, `S` the
list of safe pairs.  Moves are tuples ('sub', b, c, d, x), ('flip', b, c, d, e),
('unsub', b, c, d, x), with the same meaning and the same acceptance conditions as `Mv` in Lean.
`check` returns the final complex or raises `ChainError` naming the first rejected move.

The script also converts move lists in the format of an external search tool into this format and
prints
chains as Lean terms.  Used to verify a chain before it is written into a Lean file, where
`decide +kernel` checks it again.
"""
F = frozenset


class ChainError(Exception):
    pass


def verts(K):
    return set().union(*K) if K else set()


def safe(B, S, u, v):
    return u not in B or v not in B or (u, v) in S or (v, u) in S


def sub_res(K, b, c, d, x):
    return (K - {F({b, c, d})}) | {F({b, c, x}), F({c, d, x}), F({b, d, x})}


def flip_res(K, b, c, d, e):
    return (K - {F({b, c, d}), F({b, c, e})}) | {F({b, d, e}), F({c, d, e})}


def unsub_res(K, b, c, d, x):
    return (K - {F({b, c, x}), F({c, d, x}), F({b, d, x})}) | {F({b, c, d})}


def ok_sub(B, K, b, c, d, x):
    return (len({b, c, d}) == 3 and F({b, c, d}) in K and x not in verts(K) and x not in B)


def ok_flip(B, S, K, b, c, d, e):
    if len({b, c, d, e}) != 4:
        return False
    if F({b, c, d}) not in K or F({b, c, e}) not in K:
        return False
    if any({b, c} <= t and t not in (F({b, c, d}), F({b, c, e})) for t in K):
        return False
    if any({d, e} <= t for t in K):
        return False
    return safe(B, S, b, c) and safe(B, S, d, e)


def ok_unsub(B, S, K, b, c, d, x):
    if len({b, c, d}) != 3:
        return False
    K0 = K - {F({b, c, x}), F({c, d, x}), F({b, d, x})}
    R = K0 | {F({b, c, d})}
    if x in verts(R):
        return False
    if F({b, c, d}) in K0:
        return False
    if sub_res(R, b, c, d, x) != K:
        return False
    if x in B:
        return False
    return safe(B, S, b, c) or safe(B, S, c, d) or safe(B, S, b, d)


def step(B, S, K, mv):
    kind, b, c, d, x = mv
    if kind == 'sub':
        if not ok_sub(B, K, b, c, d, x):
            raise ChainError(f'sub rejected: {mv}')
        return sub_res(K, b, c, d, x)
    if kind == 'flip':
        if not ok_flip(B, S, K, b, c, d, x):
            raise ChainError(f'flip rejected: {mv}')
        return flip_res(K, b, c, d, x)
    if kind == 'unsub':
        if not ok_unsub(B, S, K, b, c, d, x):
            raise ChainError(f'unsub rejected: {mv}')
        return unsub_res(K, b, c, d, x)
    raise ValueError(mv)


def check(B, S, X, ms):
    K = F(F(t) for t in X)
    for i, mv in enumerate(ms):
        try:
            K = step(B, S, K, mv)
        except ChainError as e:
            raise ChainError(f'move {i}: {e}') from None
    return K


def from_ss(path):
    """Convert moves in the external search tool's format: ('sub', (a,b,c), x),
    ('flip', (b,c), (d,e)), ('remove', v, (a,b,c))."""
    out = []
    for mv in path:
        if mv[0] == 'sub':
            (a, b, c), x = mv[1], mv[2]
            out.append(('sub', a, b, c, x))
        elif mv[0] == 'flip':
            (b, c), (d, e) = mv[1], mv[2]
            out.append(('flip', b, c, d, e))
        else:
            v, (a, b, c) = mv[1], mv[2]
            out.append(('unsub', a, b, c, v))
    return out


def relabel(ms, m):
    g = lambda u: m.get(u, u)
    return [(k, g(b), g(c), g(d), g(x)) for (k, b, c, d, x) in ms]


def inverse(ms):
    """The reverse chain: sub <-> unsub; a flip bc -> de is undone by the flip de -> bc."""
    out = []
    for (k, b, c, d, x) in reversed(ms):
        if k == 'sub':
            out.append(('unsub', b, c, d, x))
        elif k == 'unsub':
            out.append(('sub', b, c, d, x))
        else:
            out.append(('flip', d, x, b, c))
    return out


def rename_moves(K, u, u2, B):
    """Moves renaming the non-boundary vertex u of the complex K (a closed region around u) to the
    fresh label u2: subdivide a triangle at u by u2, flip one edge at u, then contract u into u2 by
    flips and a final removal.  Returns the move list; `check` verifies it."""
    K = F(F(t) for t in K)
    star = [t for t in K if u in t]
    t0 = sorted(star, key=sorted)[0]
    p, q = sorted(t0 - {u})
    ms = [('sub', u, p, q, u2)]
    K = sub_res(K, u, p, q, u2)
    # the other triangle at u q: {u, q, w}
    w = next(iter(next(t for t in K if {u, q} <= t and u2 not in t) - {u, q}))
    ms.append(('flip', u, q, u2, w))
    K = flip_res(K, u, q, u2, w)
    # contract: while deg u > 3, flip an edge u-y (y not in {u2}) whose flip is allowed
    while True:
        st = [t for t in K if u in t]
        if len(st) == 3:
            a, b, c = sorted(verts(st) - {u})
            ms.append(('unsub', a, b, c, u))
            K = unsub_res(K, a, b, c, u)
            break
        done = False
        for y in sorted(verts(st) - {u, u2}):
            ts = [t for t in K if {u, y} <= t]
            if len(ts) != 2:
                continue
            d, e = [next(iter(t - {u, y})) for t in ts]
            if u2 not in (d, e):
                continue
            if any({d, e} <= t for t in K):
                continue
            ms.append(('flip', u, y, d, e))
            K = flip_res(K, u, y, d, e)
            done = True
            break
        if not done:
            raise ChainError(f'contraction of {u} into {u2} stuck')
    return ms, K


def lean_tri(t):
    return '{' + ', '.join(str(u) for u in sorted(t)) + '}'


def lean_K(K):
    return '{' + ', '.join(lean_tri(t) for t in sorted(K, key=sorted)) + '}'


def lean_ms(ms):
    names = {'sub': '.sub', 'flip': '.flip', 'unsub': '.unsub'}
    return '[' + ', '.join(f'{names[k]} {b} {c} {d} {x}' for (k, b, c, d, x) in ms) + ']'


def lean_S(S):
    return '[' + ', '.join(f'({p}, {q})' for p, q in S) + ']'


def lean_B(B):
    return '{' + ', '.join(str(u) for u in sorted(B)) + '}'
