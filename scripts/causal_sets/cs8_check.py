"""Enumeration cross-check (not a proof) of Lightlike/CausalSets/PosetCount.lean.

Labelled strict partial orders on n = 0..4 elements: 1, 1, 3, 19, 219; those with no chain of three
elements (two layers): 1, 1, 3, 13, 87. Wrong-input controls, each must be detected: counting
reflexive-closed relations without transitivity gives a different number for n = 3 (the number of
irreflexive acyclic relations is not 19); the two-layer fraction is not constant.
Exit 0 when all agree and every control is detected."""
import itertools
import sys

fails = []

def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok:
        fails.append(name)

def rels(n):
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for bits in itertools.product([0, 1], repeat=len(pairs)):
        yield {pr for pr, b in zip(pairs, bits) if b}

def is_order(r, n):
    if any((i, j) in r and (j, i) in r for i in range(n) for j in range(i + 1, n)):
        return False
    return all((i, k) in r for (i, j) in r for (j2, k) in r if j == j2 and i != k)

def two_layer(r, n):
    return not any((i, j) in r and (j, k) in r for i in range(n) for j in range(n) for k in range(n))

tot, two = [], []
for n in range(5):
    P = [r for r in rels(n) if is_order(r, n)]
    tot.append(len(P))
    two.append(sum(1 for r in P if two_layer(r, n)))
check(f"labelled orders {tot}", tot == [1, 1, 3, 19, 219])
check(f"two-layer orders {two}", two == [1, 1, 3, 13, 87])
loose = sum(1 for r in rels(3) if not any((i, j) in r and (j, i) in r for i in range(3) for j in range(i + 1, 3)))
check(f"control: antisymmetric relations without transitivity on 3 points number {loose}, not 19", loose != 19)
check("control: two-layer fraction decreases", two[4] / tot[4] < two[3] / tot[3])
if fails:
    print("FAILED:", fails)
    sys.exit(1)
print("all CS8 values agree")
