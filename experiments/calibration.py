#!/usr/bin/env python3
"""
CALIBRATION OF THE D_S INSTRUMENT against structures of KNOWN spectral dimension.

Before reading the trichotomy off CDT / melonic / causal-set spectra, validate
that the *same* running-D_S machinery the paper uses (`ds_at` on the normalized
Laplacian, flat-window plateau detection) actually measures the spectral
dimension, and is not an artifact of the heat-trace fit.

Two checks, run together:

  (1) FAITHFUL-TO-SPECTRUM.  The heat-trace plateau `ds_at` must equal the
      spectral dimension read a completely different way — the small-eigenvalue
      slope of the integrated density of states, N(lambda) ~ lambda^{d_s/2}.
      `ds_at` and the IDOS slope share no code path beyond the eigenvalues, so
      agreement means the running D_S reports the genuine small-lambda exponent.

  (2) KNOWN-VALUE.  For clean single-scale structures whose d_s is fixed by
      theory, the instrument must return that value:
        ring (cycle)       d_s = 1
        torus (2D grid)    d_s = 2
        Sierpinski gasket  d_s = 2 ln3/ln5 ~= 1.3652   (a genuine non-integer
                                                         fractal dimension)

  (caveat) COMB (backbone + teeth).  The folklore "comb d_s = 3/2" (DJW,
      "Random walks on combs", hep-th/0509191) is a *backbone-local* return
      exponent.  The heat trace measures the BULK average; for the uniform comb
      the 1D teeth are almost all the vertices and dominate the eigenvalue
      density, so the bulk/trace d_s is ~1, NOT 3/2.  Both `ds_at` and the IDOS
      slope report ~1 here — they agree with each other (instrument faithful)
      and correctly read the bulk, which simply differs from the quoted local
      value.  Kept as an explicit reminder that this instrument reads the bulk
      spectral dimension, the same quantity it reports for melonic / CDT.

Stage-B gate: (1) holds for every structure AND (2) holds for ring/torus/
Sierpinski  =>  instrument validated.  A disagreement in (1) would be a real bug.

Run:
  PYTHONPATH=<nix numpy> <nix python3.13> experiments/calibration.py
"""
import numpy as np

# ---------- the paper's instrument (identical to tail_vs_gap.py) ------------
def norm_lap_eigs(A):
    deg = A.sum(1); deg[deg == 0] = 1.0
    di = 1.0 / np.sqrt(deg)
    L = np.eye(len(A)) - di[:, None] * A * di[None, :]
    return np.clip(np.linalg.eigvalsh(0.5*(L+L.T)), 0, None)

def ds_at(ev, sig):
    e = ev[:, None]; E = np.exp(-sig[None, :]*e)
    return 2.0*sig*(e*E).sum(0)/E.sum(0)

SIG = np.logspace(-1.5, 3.0, 300)

def ds_at_plateau(ev):
    """Heat-trace running-D_S, median over the widest flat window."""
    ds = ds_at(ev, SIG)
    dlog = np.gradient(ds, np.log(SIG))
    flat = (np.abs(dlog) < 0.10) & (ds > 0.5)
    if not flat.any():
        flat = (np.abs(dlog) < 0.20) & (ds > 0.5)
    return np.median(ds[flat]) if flat.any() else np.nan

def idos_ds(ev, frac_lo=0.02, frac_hi=0.18):
    """Independent ground truth: small-lambda slope of the integrated DOS,
    N(lambda) ~ lambda^{d_s/2}; returns 2 * (log-log slope). No heat trace."""
    nz = np.sort(ev[ev > 1e-9]); m = len(nz)
    k = np.arange(1, m+1) / m
    lo, hi = int(frac_lo*m), int(frac_hi*m)
    slope = np.polyfit(np.log(nz[lo:hi]), np.log(k[lo:hi]), 1)[0]
    return 2*slope

# ---------- structures ------------------------------------------------------
def ring_adjacency(N):
    A = np.zeros((N, N))
    for i in range(N):
        A[i, (i+1) % N] = 1; A[(i+1) % N, i] = 1
    return A

def torus_adjacency(L):
    N = L*L; A = np.zeros((N, N)); idx = lambda i, j: (i % L)*L + (j % L)
    for i in range(L):
        for j in range(L):
            for di, dj in ((1, 0), (0, 1)):
                a, b = idx(i, j), idx(i+di, j+dj)
                A[a, b] = 1; A[b, a] = 1
    return A

def sierpinski_adjacency(depth):
    S = 1 << depth
    tris = [((0, 0), (S, 0), (0, S))]
    for _ in range(depth):
        new = []
        for a, b, c in tris:
            ab = ((a[0]+b[0])//2, (a[1]+b[1])//2)
            ac = ((a[0]+c[0])//2, (a[1]+c[1])//2)
            bc = ((b[0]+c[0])//2, (b[1]+c[1])//2)
            new += [(a, ab, ac), (ab, b, bc), (ac, bc, c)]
        tris = new
    vid = {}
    def gid(p):
        if p not in vid: vid[p] = len(vid)
        return vid[p]
    edges = set()
    for a, b, c in tris:
        ia, ib, ic = gid(a), gid(b), gid(c)
        for u, v in ((ia, ib), (ib, ic), (ia, ic)):
            edges.add((min(u, v), max(u, v)))
    N = len(vid); A = np.zeros((N, N))
    for u, v in edges:
        A[u, v] = 1; A[v, u] = 1
    return A

def comb_adjacency(B, Tooth):
    N = B*(1+Tooth); A = np.zeros((N, N))
    for i in range(B-1):
        A[i, i+1] = 1; A[i+1, i] = 1
    for i in range(B):
        prev = i
        for k in range(Tooth):
            v = B + i*Tooth + k
            A[prev, v] = 1; A[v, prev] = 1
            prev = v
    return A

# ---------- run -------------------------------------------------------------
SIERP = 2*np.log(3)/np.log(5)
known = [   # (name, known bulk d_s, [adjacency at growing size], gated?)
    ("ring (cycle)",        1.0,   [ring_adjacency(n) for n in (600, 1200)],          True),
    ("torus (2D grid)",     2.0,   [torus_adjacency(L) for L in (24, 34)],            True),
    ("Sierpinski gasket",   SIERP, [sierpinski_adjacency(d) for d in (5, 6)],         True),
    ("comb (bulk, teeth>>)",1.0,   [comb_adjacency(B, T) for B, T in ((10, 200), (8, 400))], False),
]

print("CALIBRATION: heat-trace D_S vs independent IDOS ground truth, and vs known d_s")
print(f"{'structure':<22} | {'N':>5} | {'known':>6} | {'IDOS d_s':>8} | {'ds_at':>6} "
      f"| {'|ds_at-IDOS|':>11} | {'|ds_at-known|':>12}")
print("-"*92)
faith_max, known_max = 0.0, 0.0
for name, kn, mats, gated in known:
    for A in mats:
        ev = norm_lap_eigs(A)
        idos, dsa = idos_ds(ev), ds_at_plateau(ev)
        faith, kerr = abs(dsa - idos), abs(dsa - kn)
        faith_max = max(faith_max, faith)
        if gated:
            known_max = max(known_max, kerr)
        tag = "" if gated else "  (caveat: bulk!=backbone-local 3/2)"
        print(f"{name:<22} | {len(A):>5} | {kn:>6.3f} | {idos:>8.3f} | {dsa:>6.3f} "
              f"| {faith:>11.3f} | {kerr:>12.3f}{tag}")
    print("-"*92)

print(f"\n(1) faithful-to-spectrum: max |ds_at - IDOS| over ALL structures = {faith_max:.3f}")
print(f"(2) known-value:          max |ds_at - known| over ring/torus/Sierpinski = {known_max:.3f}")
ok = faith_max < 0.15 and known_max < 0.10
print(f"\nGATE: instrument {'VALIDATED' if ok else 'INVESTIGATE'} "
      f"(ds_at tracks the IDOS exponent everywhere, and hits the known d_s for "
      f"clean single-scale structures incl. the non-integer Sierpinski fractal).")
