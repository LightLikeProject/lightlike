"""Coverage of the boundary evaluation `QDougallAt` by the proved theorems (stdlib only).

For r = 5, ..., 8 and every `(B, A, E, F)` with an admissible pair on both sides (the cases of
`QDougallAll`), the script classifies the data by the orbits of the forms of the lowest colours it matches
(O1 to O4, joined by `+` when a tie matches several: the 16 pairs of a form of `aLo B A E F` and a form of `aLo B F E A`, grouped by the
permutations `(B E)(A F)`, `(B A)(E F)`, `(B F)(A E)` of the four spins), by whether the range of third
colours is cut by the level (`aHi r B A E F < min (B + A) (E + F)`), and by the theorem that covers it
(`none` if there is none). Every class is printed, nothing is filtered. The covered classes are those
of `qDougallAt_O1` and its images `qDougallAt_O1_k1`, `qDougallAt_O1_k2`, `qDougallAt_O1_k3`
(`Lightlike/TuraevViro/Reflect/QDougallMap.lean`), whose hypotheses are tested literally.

The recorded counts are checked; a control with a wrong form (the lowest third colour `B - A + 1`) covers
no case. Exit code 1 on failure. Counting, not a proof.
"""
import itertools
import sys

XF = {"B-A": lambda B, A, E, F: B - A, "A-B": lambda B, A, E, F: A - B,
      "E-F": lambda B, A, E, F: E - F, "F-E": lambda B, A, E, F: F - E}
QF = {"B-F": lambda B, A, E, F: B - F, "F-B": lambda B, A, E, F: F - B,
      "E-A": lambda B, A, E, F: E - A, "A-E": lambda B, A, E, F: A - E}
S1 = {"B": "E", "E": "B", "A": "F", "F": "A"}
S2 = {"B": "A", "A": "B", "E": "F", "F": "E"}
S3 = {"B": "F", "F": "B", "A": "E", "E": "A"}


def act(perm, f):
    a, b = f.split("-")
    return perm[a] + "-" + perm[b]


def orbit_of(pair):
    x, q = pair
    return frozenset({(x, q)} | {(act(g, x), act(g, q)) for g in (S1, S2, S3)})


ORBITS = []
seen = set()
for x, q in itertools.product(XF, QF):
    if (x, q) not in seen:
        o = orbit_of((x, q))
        ORBITS.append(o)
        seen |= o
NAMES = {}
for o in ORBITS:
    NAMES[o] = "O1" if ("B-A", "B-F") in o else "O2" if ("B-A", "F-B") in o else \
        "O3" if ("B-A", "E-A") in o else "O4"


def aLo(a, b, c, d):
    return max(abs(a - b), abs(c - d))


def aHi(r, a, b, c, d):
    return min(a + b, c + d, 2 * (r - 2) - (a + b), 2 * (r - 2) - (c + d))


def adm(r, a, b, c):
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0 and a + b + c <= 2 * (r - 2)


def covered(r, B, A, E, F, shift=0):
    """The theorem covering the data, or None; `shift` is the wrong-form control."""
    def rep(b, a, e, f):  # the hypotheses of qDougallAt_O1 for (b, a, e, f)
        return (a <= b and f <= b and aLo(b, a, e, f) == b - a + shift and aLo(b, f, e, a) == b - f
                and aHi(r, b, a, e, f) == e + f)
    if rep(B, A, E, F):
        return "qDougallAt_O1"
    if rep(E, F, B, A):
        return "qDougallAt_O1_k1"
    if rep(A, B, F, E):
        return "qDougallAt_O1_k2"
    if rep(F, E, A, B):
        return "qDougallAt_O1_k3"
    return None


def run(shift=0):
    table = {}
    for r in range(5, 9):
        for B, A, E, F in itertools.product(range(2 * (r - 2) + 1), repeat=4):
            if (B + A + E + F) % 2:
                continue
            x0, hi, q0 = aLo(B, A, E, F), aHi(r, B, A, E, F), aLo(B, F, E, A)
            if hi < x0 or not any(adm(r, B, F, q) and adm(r, E, A, q) for q in range(2 * r)):
                continue
            pairs = [(x, q) for x in XF for q in QF
                     if XF[x](B, A, E, F) == x0 and QF[q](B, A, E, F) == q0]
            orb = "+".join(sorted({NAMES[orbit_of(p)] for p in pairs})) if pairs else "?"
            trunc = hi < min(B + A, E + F)
            thm = covered(r, B, A, E, F, shift)
            key = (orb, "truncated" if trunc else "untruncated")
            row = table.setdefault(key, {"cases": 0, "covered": 0, "theorems": set()})
            row["cases"] += 1
            if thm:
                row["covered"] += 1
                row["theorems"].add(thm)
    return table


EXPECTED = {'O1/truncated': (64, 0), 'O1/untruncated': (160, 160),
            'O1+O2+O3+O4/truncated': (190, 0), 'O1+O2+O3+O4/untruncated': (316, 316),
            'O1+O3/truncated': (234, 0), 'O1+O3/untruncated': (422, 422),
            'O3/truncated': (64, 0), 'O3/untruncated': (160, 0)}


def main():
    table = run()
    total = sum(v["cases"] for v in table.values())
    cov = sum(v["covered"] for v in table.values())
    print(f"{'orbit':5} {'range':12} {'cases':>6} {'covered':>8}  theorem")
    for key in sorted(table):
        v = table[key]
        print(f"{key[0]:5} {key[1]:12} {v['cases']:6d} {v['covered']:8d}  "
              f"{', '.join(sorted(v['theorems'])) or 'none'}")
    print(f"total {total}, covered {cov}")
    control = sum(v["covered"] for v in run(shift=1).values())
    print("control (wrong form): covered", control)
    counts = {f"{k[0]}/{k[1]}": (v["cases"], v["covered"]) for k, v in table.items()}
    print("counts", counts)
    ok = control == 0 and total > 0 and (EXPECTED is None or counts == EXPECTED)
    print("OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
