"""Numerical evidence for RC6 (not proof): do 2D Regge curvature measures converge to K dA?

The round unit sphere in stereographic coordinates, g = lam(x)^2 delta with lam = 2/(1+|x|^2) and
Gaussian curvature K = 1. Triangular lattices of spacing h (regular, and with every vertex moved
at random by up to 0.2 h, still fat). Edge lengths by three rules: the geodesic distance (the
secant approximation of Cheeger-Mueller-Schrader), the g-length of the straight coordinate
segment, and the midpoint rule l^2 = g(m)(dx, dx). Printed: sum_v f(v) delta_v divided by
int f K dA for h = 0.08, 0.04, 0.02, 0.01, with f = (1/4 - |x|^2)_+^3. Control: Euclidean lengths
(ignoring the metric) give 0.
"""
import math
import random
def lam(x, y): return 2 / (1 + x*x + y*y)
def P(x, y):
    r2 = x*x + y*y
    return (2*x/(1+r2), 2*y/(1+r2), (1-r2)/(1+r2))
def geo(p, q):
    a, b = P(*p), P(*q)
    d = max(-1, min(1, sum(u*v for u, v in zip(a, b))))
    return math.acos(d)
GL = [(-0.9061798459, 0.2369268851), (-0.5384693101, 0.4786286705), (0, 0.5688888889),
      (0.5384693101, 0.4786286705), (0.9061798459, 0.2369268851)]
def seg(p, q):
    dx, dy = q[0]-p[0], q[1]-p[1]; L = math.hypot(dx, dy)
    return sum(w * lam(p[0]+(t+1)/2*dx, p[1]+(t+1)/2*dy) for t, w in GL) / 2 * L
def mid(p, q):
    return lam((p[0]+q[0])/2, (p[1]+q[1])/2) * math.hypot(q[0]-p[0], q[1]-p[1])
def f(x, y):
    r2 = x*x + y*y
    return max(0.0, 0.25 - r2) ** 3
def exact():
    n = 1200; s = 0; hh = 1.0 / n
    for i in range(-n, n):
        for j in range(-n, n):
            x, y = (i+0.5)*hh, (j+0.5)*hh
            s += f(x, y) * lam(x, y)**2 * hh * hh
    return s
def regge(h, length):
    # triangular lattice: vertices a*e1 + b*e2, e1=(h,0), e2=(h/2, h*sqrt3/2)
    pts = {}
    N = int(1.2 / h) + 2
    for a in range(-2*N, 2*N):
        for b in range(-2*N, 2*N):
            x, y = a*h + b*h/2, b*h*math.sqrt(3)/2
            if x*x + y*y < 0.81: pts[(a, b)] = (x, y)
    tot = 0.0
    for (a, b), p in pts.items():
        if f(*p) == 0: continue
        nb = [(a+1, b), (a, b+1), (a-1, b+1), (a-1, b), (a, b-1), (a+1, b-1)]
        ang = 0.0
        for k in range(6):
            q, r = pts[nb[k]], pts[nb[(k+1) % 6]]
            A, B, C = length(p, q), length(p, r), length(q, r)
            ang += math.acos((A*A + B*B - C*C) / (2*A*B))
        tot += f(*p) * (2*math.pi - ang)
    return tot
def regge_jitter(h, length, jit, seed=1):
    rnd = random.Random(seed)
    pts = {}
    N = int(1.2 / h) + 2
    for a in range(-2*N, 2*N):
        for b in range(-2*N, 2*N):
            x, y = a*h + b*h/2, b*h*math.sqrt(3)/2
            if x*x + y*y < 0.81:
                pts[(a, b)] = (x + jit*h*rnd.uniform(-1, 1), y + jit*h*rnd.uniform(-1, 1))
    tot = 0.0
    for (a, b), p in pts.items():
        if f(*p) == 0: continue
        nb = [(a+1, b), (a, b+1), (a-1, b+1), (a-1, b), (a, b-1), (a+1, b-1)]
        ang = 0.0
        for k in range(6):
            q, r = pts[nb[k]], pts[nb[(k+1) % 6]]
            A, B, C = length(p, q), length(p, r), length(q, r)
            ang += math.acos((A*A + B*B - C*C) / (2*A*B))
        tot += f(*p) * (2*math.pi - ang)
    return tot
def euclid(p, q): return math.hypot(q[0]-p[0], q[1]-p[1])
E = exact()
print("int f K dA =", E)
for name, L in [("geodesic", geo), ("segment", seg), ("midpoint", mid), ("euclid (control)", euclid)]:
    print(f"{name:17s} regular", [round(regge(h, L) / E, 5) for h in (0.08, 0.04, 0.02, 0.01)])
    print(f"{name:17s} jitter ", [round(regge_jitter(h, L, 0.2) / E, 5) for h in (0.08, 0.04, 0.02, 0.01)])

# Non-constant curvature: g = exp(2 phi) delta, phi = 0.3 x y + 0.2 x^2, K = -0.4 exp(-2 phi)
# (no closed-form geodesic distance, so only the segment and midpoint rules).
def phi(x, y): return 0.3*x*y + 0.2*x*x
def lam(x, y): return math.exp(phi(x, y))
def Kc(x, y): return -0.4 * math.exp(-2 * phi(x, y))
n = 1200; hh = 1.0 / n
E2 = sum(f((i+0.5)*hh, (j+0.5)*hh) * Kc((i+0.5)*hh, (j+0.5)*hh) * lam((i+0.5)*hh, (j+0.5)*hh)**2
         * hh * hh for i in range(-n, n) for j in range(-n, n))
print("varying K: int f K dA =", E2)
for name, L in [("segment", seg), ("midpoint", mid)]:
    print(f"{name:17s} regular", [round(regge(h, L) / E2, 5) for h in (0.08, 0.04, 0.02, 0.01)])
    print(f"{name:17s} jitter ", [round(regge_jitter(h, L, 0.2) / E2, 5) for h in (0.08, 0.04, 0.02, 0.01)])
