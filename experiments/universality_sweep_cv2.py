#!/usr/bin/env python3
"""
Universality sweep for the kinematic-floor hypothesis  (grounds the "growing
spectral gap => CV^2 -> 0" leg of the universal constraint theorem).

Claim under test:  CV^2(pairwise distances) -> 0 across DIVERSE growing-spectral-gap
(Levy) families, and STAYS BOUNDED for bounded-dimension local-geometry families.
CV^2 := Var[d]/E[d]^2  (same definition as cpn_concentration.jl; scale-invariant).

Once CV^2 -> 0 the metric graph -> complete graph K_m, and the heat-trace probe on
K_m reads D_S(1) -> 2  (machine-checked: completeGraph_spectralDimension_two, Lean,
0-axiom). So the universality of "=> 2" reduces to the universality of CV^2 -> 0,
which is what this sweep measures.  Pure Python, no deps.

Cross-check: CP^n must reproduce CV^2 ~ (4-pi)/(pi^2 n) (see cv2_asymptotic_verify.py
and cpn_concentration.csv).
"""
import math, random

rng = random.Random(7)
M = 200                       # states/points sampled per (family, param)


def _cv2(dists):
    n = len(dists)
    mu = sum(dists) / n
    var = sum((x - mu) ** 2 for x in dists) / n
    mx = max(abs(x - mu) for x in dists) / mu
    return var / (mu * mu), mx


def _pairwise(points, metric):
    ds = []
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            ds.append(metric(points[i], points[j]))
    return ds


# ---- Levy families (growing spectral gap => should concentrate) ----
def sphere(d, m):                                   # S^d, geodesic distance
    pts = []
    for _ in range(m):
        v = [rng.gauss(0, 1) for _ in range(d + 1)]
        nrm = math.sqrt(sum(x * x for x in v))
        pts.append([x / nrm for x in v])
    dot = lambda a, b: max(-1.0, min(1.0, sum(x * y for x, y in zip(a, b))))
    return _pairwise(pts, lambda a, b: math.acos(dot(a, b)))


def cpn(n, m):                                      # CP^n, Fubini-Study distance
    pts = []
    for _ in range(m):
        re = [rng.gauss(0, 1) for _ in range(n + 1)]
        im = [rng.gauss(0, 1) for _ in range(n + 1)]
        nrm = math.sqrt(sum(a * a + b * b for a, b in zip(re, im)))
        pts.append(([a / nrm for a in re], [b / nrm for b in im]))
    def fs(a, b):
        ar, ai = a; br, bi = b
        # |<a|b>| = | sum conj(a_k) b_k |
        rr = sum(x * u + y * v for x, y, u, v in zip(ar, ai, br, bi))
        ii = sum(x * v - y * u for x, y, u, v in zip(ar, ai, br, bi))
        return math.acos(max(0.0, min(1.0, math.sqrt(rr * rr + ii * ii))))
    return _pairwise(pts, fs)


def hypercube(d, m):                                # {0,1}^d, Hamming distance
    pts = [[rng.randint(0, 1) for _ in range(d)] for _ in range(m)]
    return _pairwise(pts, lambda a, b: sum(x != y for x, y in zip(a, b)))


# ---- Local-geometry controls (bounded dimension => should NOT concentrate) ----
def cycle(L, m):                                    # C_L, 1D ring distance
    verts = list(range(L)) if L <= m else rng.sample(range(L), m)
    return _pairwise(verts, lambda i, j: min(abs(i - j), L - abs(i - j)))


def torus2d(L, m):                                  # Z_L x Z_L, toroidal Manhattan
    allv = [(x, y) for x in range(L) for y in range(L)]
    verts = allv if len(allv) <= m else rng.sample(allv, m)
    def dist(a, b):
        dx = abs(a[0] - b[0]); dy = abs(a[1] - b[1])
        return min(dx, L - dx) + min(dy, L - dy)
    return _pairwise(verts, dist)


FAMILIES = [
    ("S^d  (sphere)", "d", sphere, [2, 4, 8, 16, 32, 64, 128], "Levy"),
    ("CP^n (Fubini-Study)", "n", cpn, [2, 5, 10, 20, 50, 100], "Levy"),
    ("Q_d  (hypercube)", "d", hypercube, [4, 8, 16, 32, 64, 128], "Levy"),
    ("C_L  (1D cycle)", "L", cycle, [16, 64, 256, 1024], "local-dim-1"),
    ("Z_L^2 (2D torus)", "L", torus2d, [8, 16, 32, 64], "local-dim-2"),
]

if __name__ == "__main__":
    print(f"M = {M} points per cell.  CV^2 := Var[d]/E[d]^2.\n")
    for name, pname, fn, params, kind in FAMILIES:
        print(f"=== {name}   [{kind}] ===")
        print(f"   {pname:>5} {'CV^2':>12} {'max_dev':>9} {'param*CV^2':>11}")
        for p in params:
            ds = fn(p, M)
            cv2, mx = _cv2(ds)
            print(f"   {p:>5} {cv2:>12.6e} {mx:>9.4f} {p * cv2:>11.5f}")
        print()
    print("Expected: Levy families CV^2 -> 0 (param*CV^2 -> family constant);")
    print("controls CV^2 -> a BOUNDED nonzero constant (no concentration).")
    print("CP^n cross-check: n*CV^2 -> (4-pi)/pi^2 = %.5f." % ((4 - math.pi) / math.pi ** 2))
