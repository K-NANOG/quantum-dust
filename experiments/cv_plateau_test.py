#!/usr/bin/env python3
"""
ADVERSARIAL plateau test for the dust->2 claim.

The paper asserts (unproved, not machine-checked) that the *distance-weighted*
CP^n graph has a running spectral dimension D_S(sigma) that PLATEAUS near 2 over
a wide window of scale -- "just short of" the K_m collapse. This script builds
that exact object and tests whether the plateau is real or a fitted artifact.

Object:
  - m Haar-random pure states in C^{n+1}  (overlap |<i|j>|^2 ~ Beta(1,n), matching paper)
  - Fubini-Study distance d_ij = arccos|<i|j>|
  - weighted graph w_ij = exp(-d_ij^2 / eps),  w_ii=0
  - normalized Laplacian L = I - D^{-1/2} W D^{-1/2}  (spectrum in [0,2]; K_m gives {0, m/(m-1)})
  - heat trace P(sigma) = (1/m) sum_k e^{-sigma lambda_k}
  - running spectral dimension  D_S(sigma) = -2 dlnP/dlnsigma = 2 sigma * <lambda>_sigma

Plateau width := decades of log10(sigma) with |D_S(sigma) - 2| < band.
NULL control  := the matched complete graph K_m, eigenvalues {0, (m/(m-1)) x (m-1)}.
A genuine plateau must (1) survive eps swept across decades, (2) not shrink as n
grows at fixed m, (3) be materially wider than the K_m crossing. Otherwise it is
"crossing with good PR."
"""
import numpy as np

rng = np.random.default_rng(20260616)

# ---- core ------------------------------------------------------------------
def sample_states(m, n):
    d = n + 1                                   # C^{n+1}  -> Beta(1,n)
    Z = rng.standard_normal((m, d)) + 1j * rng.standard_normal((m, d))
    Z /= np.linalg.norm(Z, axis=1, keepdims=True)
    return Z

def fs_distmat(Z):
    G = np.abs(Z @ Z.conj().T)
    np.clip(G, 0.0, 1.0, out=G)
    D = np.arccos(G)
    np.fill_diagonal(D, 0.0)
    return D

def norm_lap_eigs(W):
    W = W.copy(); np.fill_diagonal(W, 0.0)
    deg = W.sum(1)
    if (deg <= 0).any():
        return None
    dinv = 1.0 / np.sqrt(deg)
    L = np.eye(W.shape[0]) - (dinv[:, None] * W * dinv[None, :])
    L = 0.5 * (L + L.T)
    ev = np.linalg.eigvalsh(L)
    return np.clip(ev, 0.0, None)

def km_eigs(m):
    ev = np.full(m, m / (m - 1.0)); ev[0] = 0.0
    return ev

SIG = np.logspace(-3, 4, 281)                   # ~40 pts/decade over 7 decades
DLOG = (np.log10(SIG[-1]) - np.log10(SIG[0])) / (len(SIG) - 1)

def ds_curve(ev):
    e = ev[:, None]
    E = np.exp(-SIG[None, :] * e)                # (m, S)
    den = E.sum(0)
    num = (e * E).sum(0)
    return 2.0 * SIG * num / den

def width(ds, band):
    return float(np.count_nonzero(np.abs(ds - 2.0) < band)) * DLOG

# ---- experiment helpers ----------------------------------------------------
EPS_GRID = np.logspace(-2.0, 1.0, 13)           # eps swept across 3 decades

def best_eps_width(n, m, trials=3, band=0.2):
    """For each eps, mean plateau width over trials; return (best_width, best_eps, table)."""
    table = []
    for eps in EPS_GRID:
        ws = []
        for _ in range(trials):
            Z = sample_states(m, n)
            D = fs_distmat(Z)
            ev = norm_lap_eigs(np.exp(-(D ** 2) / eps))
            if ev is None:
                continue
            ws.append(width(ds_curve(ev), band))
        if ws:
            table.append((eps, float(np.mean(ws))))
    best = max(table, key=lambda t: t[1])
    return best[1], best[0], table

def km_width(m, band=0.2):
    return width(ds_curve(km_eigs(m)), band)

def ds_table(ev, npts=18):
    ds = ds_curve(ev)
    idx = np.linspace(0, len(SIG) - 1, npts).astype(int)
    return [(SIG[i], ds[i]) for i in idx]

# ---- run -------------------------------------------------------------------
print("=" * 74)
print("REPRESENTATIVE D_S(sigma) CURVE  (n=20, m=400, eps=median d^2 vs best eps)")
print("=" * 74)
Z = sample_states(400, 20); D = fs_distmat(Z)   # m=400 states, n=20
eps_med = float(np.median((D[np.triu_indices(400, 1)]) ** 2))
ev_med = norm_lap_eigs(np.exp(-(D ** 2) / eps_med))
bw, be, _ = best_eps_width(20, 400, trials=2)
ev_best = norm_lap_eigs(np.exp(-(D ** 2) / be))
ev_km = km_eigs(400)
print(f"  eps_median = {eps_med:.3f} ,  best-window eps = {be:.3f}")
print(f"  {'log10 sig':>10} | {'D_S(eps_med)':>13} {'D_S(eps_best)':>14} {'D_S(K_m)':>10}")
tm, tb, tk = ds_table(ev_med), ds_table(ev_best), ds_table(ev_km)
for (s, a), (_, b), (_, c) in zip(tm, tb, tk):
    star_a = " *" if abs(a - 2) < 0.2 else "  "
    star_b = " *" if abs(b - 2) < 0.2 else "  "
    star_c = " *" if abs(c - 2) < 0.2 else "  "
    print(f"  {np.log10(s):>10.2f} | {a:>11.3f}{star_a} {b:>12.3f}{star_b} {c:>8.3f}{star_c}")
print(f"  width|D_S-2|<0.2 (decades):  eps_med={width(ds_curve(ev_med),0.2):.3f}"
      f"  eps_best={width(ds_curve(ev_best),0.2):.3f}  K_m(null)={km_width(400):.3f}")

print()
print("=" * 74)
print("Q1  eps-SURVIVAL  (n=20, m=400): plateau width vs kernel width eps")
print("=" * 74)
_, _, tbl = best_eps_width(20, 400, trials=3)
print(f"  {'eps':>8} | {'width|D_S-2|<0.2 (decades)':>28}")
for eps, w in tbl:
    bar = "#" * int(round(w / 0.05))
    print(f"  {eps:>8.3f} | {w:>8.3f}   {bar}")
print(f"  [null] K_m crossing width = {km_width(400):.3f} decades")

print()
print("=" * 74)
print("Q2  n-SCALING  (m=400 fixed): does best-case plateau widen or shrink with n?")
print("=" * 74)
print(f"  {'n':>5} | {'best width':>11} {'@eps':>8} | {'K_m null':>9} | {'excess':>8}")
for n in [5, 20, 80, 320]:
    bw, be, _ = best_eps_width(n, 400, trials=3)
    kw = km_width(400)
    print(f"  {n:>5} | {bw:>11.3f} {be:>8.3f} | {kw:>9.3f} | {bw-kw:>8.3f}")

print()
print("=" * 74)
print("Q3  m-SCALING  (n=20 fixed): does plateau widen or shrink with sample size m?")
print("=" * 74)
print(f"  {'m':>5} | {'best width':>11} {'@eps':>8} | {'K_m null':>9} | {'excess':>8}")
for m in [100, 200, 400, 800]:
    bw, be, _ = best_eps_width(20, m, trials=3)
    kw = km_width(m)
    print(f"  {m:>5} | {bw:>11.3f} {be:>8.3f} | {kw:>9.3f} | {bw-kw:>8.3f}")

print()
print("VERDICT KEY: 'excess' = best weighted-graph width - K_m crossing width.")
print("  plateau REAL  <=> excess >> 0, stable across eps, and non-decreasing in n.")
print("  plateau = PR  <=> excess ~ 0 or needs a tuned eps or shrinks with n.")
