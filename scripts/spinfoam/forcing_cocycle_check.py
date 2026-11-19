"""Numerical check (not a proof): forcing sets and 2-cocycles over the field with two elements.

Proved in Lean (`Lightlike/SpinFoam/ForcingBlocking.lean`): a set `T` of triangles that forces every
triangle meets every nonempty set `X` of triangles with an even number of triangles in each tetrahedron
(a 2-cocycle over F2), so `|T| >= dim Z^2(K; F2)`. Here, numerically:

1. (observed) On the boundary of the 5-simplex and on three 4-spheres reached from it by Pachner
   moves, `dim Z^2 = E - V + 1`, and random minimal forcing sets have exactly that size.
2. (observed) The converse is false. A set `T` of triangles whose restriction to `Z^2` is injective
   need not force: `find_counterexample` takes the 4-sphere reached from the boundary of the 5-simplex
   by `STEPS` random 1-5, 2-4 and 3-3 moves (`forcechain.m15`, `m24`, `m33`, with
   `random.Random(SEED)`), removes triangles in a random order while the restriction stays injective,
   and reports the first minimal injective set that does not force. The first one over the seeds
   0, 1, 2, ... is seed 91, try 14 (a minimal injective set of 37 triangles that does not force); the
   self-test reproduces it.
Exit code 0 when the self-test (a forcing set is injective, a non-injective set does not force, the
pinned instance is a counterexample) passes.
"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import forcechain as F

fs = frozenset


def sphere(seed, steps):
    """The 4-sphere after `steps` random forward moves from the boundary of the 5-simplex."""
    rng = random.Random(seed)
    K, T, nv = F.start()[0], F.start()[1], 6
    for _ in range(steps):
        r = rng.choice(["15", "24", "33"])
        if r == "15":
            K, T = F.m15(K, T, nv, rng)
            nv += 1
        else:
            o = (F.m24 if r == "24" else F.m33)(K, T, rng)
            if o:
                K, T = o
    return K, rng


def cocycles(K):
    """Triangles in order, their positions, and a basis of the F2 2-cocycles (bit masks)."""
    tris = sorted(F.faces(K, 3), key=sorted)
    ti = {t: i for i, t in enumerate(tris)}
    rows = [sum(1 << ti[fs(c)] for c in itertools.combinations(sorted(t), 3))
            for t in sorted(F.faces(K, 4), key=sorted)]
    piv = {}
    for r in rows:
        for p, b in piv.items():
            if r >> p & 1:
                r ^= b
        if r:
            p = r.bit_length() - 1
            for q in list(piv):
                if piv[q] >> p & 1:
                    piv[q] ^= r
            piv[p] = r
    basis = []
    for fr in (i for i in range(len(tris)) if i not in piv):
        x = 1 << fr
        for p, b in piv.items():
            if b >> fr & 1:
                x |= 1 << p
        basis.append(x)
    return tris, ti, basis


def injective(ti, basis, T):
    """The restriction of the cocycles to `T` is injective."""
    mask = sum(1 << ti[t] for t in T)
    bs = []
    for b in basis:
        v = b & mask
        for x in bs:
            v = min(v, v ^ x)
        if v:
            bs.append(v)
    return len(bs) == len(basis)


def minimal_injective(tris, ti, basis, rng):
    order = tris[:]
    rng.shuffle(order)
    S = set(tris)
    for f in order:
        if injective(ti, basis, S - {f}):
            S.discard(f)
    return S


def find_counterexample(steps=12, seeds=range(200), tries=30):
    """First (sphere seed, try number, K, T): T minimal with injective restriction, T does not force."""
    for sd in seeds:
        K, rng = sphere(sd, steps)
        tris, ti, basis = cocycles(K)
        for k in range(tries):
            S = minimal_injective(tris, ti, basis, rng)
            if not F.forces(K, S):
                return sd, k, K, S
    return None


# Pinned instance, found by `find_counterexample(steps=12)` over the seeds 0, 1, 2, ...: the first one
# is the sphere of seed 91 and the try number 14 (a 37-triangle minimal injective set that does not force).
STEPS, SEED, TRY = 12, 91, 14


def main():
    # 1. dim Z^2 = E - V + 1 and sizes of random minimal forcing sets
    for name, (sd, st) in {"sphere 0": (0, 0), "sphere 1": (1, 4), "sphere 2": (2, 8),
                           "sphere 3": (3, 12)}.items():
        K, rng = sphere(sd, st)
        tris, ti, basis = cocycles(K)
        E, V = len(F.faces(K, 2)), len(F.faces(K, 1))
        sizes = {len(F.minimal_forcing(K, rng)) for _ in range(10)}
        print(name, ": dim Z^2 =", len(basis), ", E - V + 1 =", E - V + 1, ", minimal forcing sizes", sizes)
        assert len(basis) == E - V + 1 and sizes == {len(basis)}
    # 2. self-test: a forcing set is injective; a non-injective set does not force
    K, rng = sphere(1, 4)
    tris, ti, basis = cocycles(K)
    T = F.minimal_forcing(K, rng)
    assert F.forces(K, T) and injective(ti, basis, T)
    T2 = set(T)
    T2.discard(next(iter(T2)))
    assert not injective(ti, basis, T2) and not F.forces(K, T2)
    # 3. the converse counterexample
    res = find_counterexample(STEPS, seeds=[SEED], tries=TRY + 1)
    assert res is not None and res[:2] == (SEED, TRY), "the pinned counterexample is not reproduced"
    sd, k, K, S = res
    tris, ti, basis = cocycles(K)
    assert injective(ti, basis, S) and not F.forces(K, S) and len(S) == len(basis)
    print("converse counterexample: sphere seed", sd, "after", STEPS, "moves, try", k,
          ": minimal injective set of", len(S), "triangles that does not force")
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
