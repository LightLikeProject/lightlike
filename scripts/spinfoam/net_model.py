"""Structural model of Lightlike/SpinFoam/SNet.lean, for finding the reduction tables of a
Pachner move (search aid, not a proof: Lean checks every step it produces).

A network has edges (face, kap, live), nodes (tet, live, legs[4], neg[4]), constraints
(e1, e2, b) and a constant list `cst` of faces. Faces are frozensets of vertices.
The rewrites mirror `glue`, `loop`, `subst`/`elimN`, `flipNode`, `flipVar`, `addParity`.

Run: python3 -I scripts/spinfoam/net_model.py   (self-test: the 3-3 move reduces to the same
shape on both sides up to a GF(2) gauge)
"""
import itertools
from collections import Counter

# Vertex network of a 4-simplex on positions 0..4 (Lightlike/SpinFoam/SNet.lean).
VTRI_P = [0, 0, 0, 0, 2, 1, 2, 1, 3, 1]
VTRI_Q = [2, 4, 1, 3, 4, 2, 3, 4, 4, 3]
VLEG = [[2, 0, 3, 1], [2, 5, 9, 7], [0, 5, 6, 4], [3, 9, 6, 8], [1, 7, 4, 8]]
VNEG = [[0, 1, 0, 1], [1, 1, 0, 1], [0, 0, 0, 1], [1, 1, 1, 1], [0, 0, 0, 0]]


class Net:
    def __init__(self):
        self.eface = {}   # edge -> face
        self.kap = {}
        self.elive = {}
        self.tet = {}     # node -> face
        self.nlive = {}
        self.leg = {}     # node -> list of 4 edges
        self.neg = {}     # node -> list of 4 bools
        self.cons = []
        self.cst = []

    def copy(self):
        n = Net()
        n.eface = dict(self.eface); n.kap = dict(self.kap); n.elive = dict(self.elive)
        n.tet = dict(self.tet); n.nlive = dict(self.nlive)
        n.leg = {k: list(v) for k, v in self.leg.items()}
        n.neg = {k: list(v) for k, v in self.neg.items()}
        n.cons = list(self.cons); n.cst = list(self.cst)
        return n

    # --- rewrites -------------------------------------------------------------------------
    def glue(self, n1, n2):
        s = self.copy()
        s.nlive[n1] = False; s.nlive[n2] = False
        new = [(self.leg[n1][l], self.leg[n2][l], self.neg[n1][l] != self.neg[n2][l])
               for l in range(4)]
        s.cons = new + s.cons
        return s

    def loop(self, n1, n2, lA):
        s = self.glue(n1, n2)
        eA = self.leg[n1][lA]
        s.elive[eA] = False
        fA = self.eface[eA]
        s.cst = [f for f in s.cst if f != fA]
        return s

    def elim1(self):
        if not self.cons:
            return self
        (e1, e2, b), rest = self.cons[0], self.cons[1:]
        s = self.copy()
        if e1 == e2:
            assert not b, 'constraint x = -x'
            s.cons = rest
            return s
        # the checks of `elimOK` in SNet.lean
        assert self.elive[e1] and self.elive[e2] and self.eface[e1] == self.eface[e2]
        assert all(c[0] != e2 and c[1] != e2 for c in rest), 'e2 occurs in later constraints'
        s.kap[e1] = self.kap[e1] != self.kap[e2]
        s.elive[e2] = False
        for n in s.leg:
            for l in range(4):
                if self.leg[n][l] == e2:
                    s.leg[n][l] = e1
                    s.neg[n][l] = self.neg[n][l] != b
        s.cons = rest
        if self.kap[e2] and b:
            s.cst = [self.eface[e2]] + s.cst
        return s

    def elim_all(self):
        s = self
        while s.cons:
            s = s.elim1()
        return s

    def flip_node(self, n0):
        s = self.copy()
        for e in set(self.leg[n0]):
            s.kap[e] = not self.kap[e]
        add = [self.eface[self.leg[n0][l]] for l in range(4) if not self.neg[n0][l]]
        s.neg[n0] = [not x for x in self.neg[n0]]
        s.cst = s.cst + add
        return s

    def flip_var(self, e0):
        s = self.copy()
        for n in s.leg:
            for l in range(4):
                if self.leg[n][l] == e0:
                    s.neg[n][l] = not self.neg[n][l]
        s.cons = [(c1, c2, b != ((c1 == e0) != (c2 == e0))) for (c1, c2, b) in self.cons]
        if self.elive[e0] and self.kap[e0]:
            s.cst = [self.eface[e0]] + s.cst
        return s

    def add_parity(self, n0):
        s = self.copy()
        s.cst = s.cst + [self.eface[self.leg[n0][l]] for l in range(4)]
        return s

    # --- views ----------------------------------------------------------------------------
    def live_nodes(self):
        return [n for n in self.nlive if self.nlive[n]]

    def live_edges(self):
        return [e for e in self.elive if self.elive[e]]


def vnet(tag, fc, tt):
    """Vertex network; `fc[e]`, `tt[i]` are faces; edge/node names are (tag, index)."""
    s = Net()
    for e in range(10):
        s.eface[(tag, e)] = fc[e]; s.kap[(tag, e)] = True; s.elive[(tag, e)] = True
    for i in range(5):
        s.tet[(tag, i)] = tt[i]; s.nlive[(tag, i)] = True
        s.leg[(tag, i)] = [(tag, VLEG[i][l]) for l in range(4)]
        s.neg[(tag, i)] = [bool(VNEG[i][l]) for l in range(4)]
    return s


def union(nets):
    s = Net()
    for t in nets:
        s.eface.update(t.eface); s.kap.update(t.kap); s.elive.update(t.elive)
        s.tet.update(t.tet); s.nlive.update(t.nlive); s.leg.update(t.leg); s.neg.update(t.neg)
        s.cons += t.cons; s.cst += t.cst
    return s


def simplex_net(tag, W, drop):
    """Vertex network of the 4-simplex W \\ {drop} (W sorted tuple of 6 vertices)."""
    pos = [v for v in W if v != drop]
    fc = [frozenset(v for v in pos if v not in (pos[VTRI_P[e]], pos[VTRI_Q[e]])) for e in range(10)]
    tt = [frozenset(v for v in pos if v != pos[i]) for i in range(5)]
    return vnet(tag, fc, tt)


def cst_parity(s):
    return {f for f, c in Counter(s.cst).items() if c % 2}


def node_key(s, n):
    return (s.tet[n], tuple(s.eface[e] for e in s.leg[n]))


def summary(s):
    """A coarse invariant: live nodes by (tet, leg faces), live edges by face."""
    return (sorted(map(lambda n: node_key(s, n), s.live_nodes()), key=repr),
            sorted((repr(s.eface[e]) for e in s.live_edges())))


if __name__ == '__main__':
    W = tuple(range(6))
    # 3-3: A = {0,1,2}-side ... three simplices W \ {b}, b in B = (3,4,5)
    nets = [simplex_net(k, W, b) for k, b in enumerate((3, 4, 5))]
    U = union(nets)
    print('nodes', len(U.live_nodes()), 'edges', len(U.live_edges()))
    # glue block 1 node opposite 5 with block 2 node opposite 4: both tets are W\{4,5}
    def node_of(s, k, tet):
        return next(n for n in s.nlive if n[0] == k and s.tet[n] == tet)
    t = frozenset(W) - {4, 5}
    G = U.glue(node_of(U, 1, t), node_of(U, 2, t))
    print('glued: live nodes', len(G.live_nodes()), 'cons', len(G.cons))
    N = G.elim_all()
    print('after elim: live edges', len(N.live_edges()), 'cst', cst_parity(N))
