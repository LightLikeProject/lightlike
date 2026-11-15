"""GF(2) gauge matching of two reduced networks (search aid; Lean checks the result).
Given P (reduced side) and Q (target) with the same live nodes/edges (nodes matched by tet,
edges by face), find node flips f, variable flips g and parities p so that
addParities(flipVars(flipNodes(P, f), g), p) has the signs, flags and constant sign of Q."""
import sys
sys.path.insert(0, 'scripts/spinfoam')
from net_model import *

def solve_gf2(rows, nvars):
    """rows: list of (bitmask over vars, rhs bit). Returns solution bitmask or None."""
    piv = {}
    for m, r in rows:
        for p, (pm, pr) in piv.items():
            if m >> p & 1: m ^= pm; r ^= pr
        if m == 0:
            if r: return None
            continue
        p = m.bit_length() - 1
        for q in list(piv):
            pm, pr = piv[q]
            if pm >> p & 1: piv[q] = (pm ^ m, pr ^ r)
        piv[p] = (m, r)
    sol = 0
    for p, (pm, pr) in piv.items():
        if pr: sol |= 1 << p
    return sol

def match(P, Q, drop_edges=()):
    nodesP = {P.tet[n]: n for n in P.live_nodes()}
    nodesQ = {Q.tet[n]: n for n in Q.live_nodes()}
    if set(nodesP) != set(nodesQ): return None, 'node sets differ'
    edgeP = {P.eface[e]: e for e in P.live_edges() if e not in drop_edges}
    edgeQ = {Q.eface[e]: e for e in Q.live_edges()}
    if set(edgeP) != set(edgeQ): return None, 'edge sets differ'
    tets = sorted(nodesP, key=lambda t: sorted(t))
    faces = sorted(edgeP, key=lambda t: sorted(t))
    for t in tets:
        if [P.eface[e] for e in P.leg[nodesP[t]]] != [Q.eface[e] for e in Q.leg[nodesQ[t]]]:
            return None, 'leg faces differ at %s' % sorted(t)
    nv = {('f', t): i for i, t in enumerate(tets)}
    k = len(tets)
    for i, f in enumerate(faces): nv[('g', f)] = k + i
    k += len(faces)
    for i, t in enumerate(tets): nv[('p', t)] = k + i
    k += len(tets)
    rows = []
    # signs of legs
    for t in tets:
        nP, nQ = nodesP[t], nodesQ[t]
        for l in range(4):
            f = P.eface[P.leg[nP][l]]
            rows.append(((1 << nv[('f', t)]) | (1 << nv[('g', f)]), int(P.neg[nP][l] != Q.neg[nQ][l])))
    # flags
    for f in faces:
        m = 0
        for t in tets:
            if f in {P.eface[e] for e in P.leg[nodesP[t]]}: m ^= 1 << nv[('f', t)]
        rows.append((m, int(P.kap[edgeP[f]] != Q.kap[edgeQ[f]])))
    # constant sign: P.cst + effects == Q.cst (as parity sets of faces); effects linear
    allf = set(cst_parity(P)) | set(cst_parity(Q))
    for t in tets:
        allf |= {P.eface[e] for e in P.leg[nodesP[t]]}
    for f in faces: allf.add(f)
    for fc in allf:
        m = 0
        for t in tets:
            n = nodesP[t]
            if any(P.eface[P.leg[n][l]] == fc and not P.neg[n][l] for l in range(4)): m ^= 1 << nv[('f', t)]
            if any(P.eface[P.leg[n][l]] == fc for l in range(4)): m ^= 1 << nv[('p', t)]
        if fc in edgeQ or fc in edgeP:
            if Q.kap[edgeQ[fc]]: m ^= 1 << nv[('g', fc)]
        rows.append((m, int((fc in cst_parity(P)) != (fc in cst_parity(Q)))))
    sol = solve_gf2(rows, k)
    if sol is None: return None, 'no gauge'
    fl = [t for t in tets if sol >> nv[('f', t)] & 1]
    gv = [f for f in faces if sol >> nv[('g', f)] & 1]
    pa = [t for t in tets if sol >> nv[('p', t)] & 1]
    return (fl, gv, pa, nodesP, edgeP), 'ok'

def apply(P, fl, gv, pa, nodesP, edgeP):
    s = P
    for t in fl: s = s.flip_node(nodesP[t])
    for f in gv: s = s.flip_var(edgeP[f])
    for t in pa: s = s.add_parity(nodesP[t])
    return s

def same(P, Q):
    nodesQ = {Q.tet[n]: n for n in Q.live_nodes()}
    ok = True
    for n in P.live_nodes():
        m = nodesQ[P.tet[n]]
        ok &= P.neg[n] == Q.neg[m]
    eQ = {Q.eface[e]: e for e in Q.live_edges()}
    for e in P.live_edges():
        if P.eface[e] in eQ: ok &= P.kap[e] == Q.kap[eQ[P.eface[e]]]
    return ok and cst_parity(P) == cst_parity(Q)
