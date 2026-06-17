#!/usr/bin/env python3
"""
Reproducible N-series for the causal-set Class-B claims of Section V, and the
two crossing chords quoted there. This is the referee-answer artifact: every
number Section V states about the causal set is recomputed here from the same
Python `causal()` generator used for Fig. 1 (seed 7).

What it produces (run output, seed 7):

  FIGURE realization (cdt pre-roll, then causal(576) -- matches Fig. 1):
    normalized crossing chord  = 1.757  -> Section V "slope 1.76"
    combinatorial crossing chord = 1.585 -> Section V "1.58"

  BAND across N (fresh default_rng(7), causal(N) direct):
    N      p:q          rho=b/a   norm_chord   gapfrac(<0.1)=1/N
    64     36:27        1.95      1.51         0.0156
    256    153:102      1.73      1.71         0.0039
    576    336:239      1.68      1.76         0.0017
    1024   588:435      1.64      1.79         0.0010
    2025   1146:878     1.60      1.81         0.0005

Reading: both scales stay macroscopically populated (p, q each O(m)) across the
whole range -> the band never collapses to a single cluster; rho drifts
1.95 -> 1.60, i.e. slowly toward the dust value 1 (the strict N->inf limit is
not settled at these sizes); the near-zero fraction is exactly 1/N (the lone
zero mode), confirming the gap. The paper's hedged "near 592:431 at N=1024"
and "rho approx 1.7" are single-realization values within this noise.

Run:
  PYTHONPATH=<nix python3.13-numpy site-packages> <nix python3.13> \
      experiments/causal_band_Nseries.py
"""
import numpy as np

# --- generators (verbatim from fig_trichotomy_data.py; RNG-equivalent) -------
def cdt_adjacency(N_s, T, p, rng):
    N = N_s * T; A = np.zeros((N, N)); v = lambda t, s: t * N_s + s
    for t in range(T):
        for s in range(N_s):
            A[v(t, s), v(t, (s+1) % N_s)] = 1; A[v(t, (s+1) % N_s), v(t, s)] = 1
        tn = (t+1) % T
        for s in range(N_s):
            sn = (s+1) % N_s
            A[v(t, s), v(tn, s)] = 1; A[v(tn, s), v(t, s)] = 1
            if rng.random() < p:
                A[v(t, sn), v(tn, s)] = 1; A[v(tn, s), v(t, sn)] = 1
            else:
                A[v(t, s), v(tn, sn)] = 1; A[v(tn, sn), v(t, s)] = 1
    np.fill_diagonal(A, 0); return np.minimum(A, 1.0)

def causal(N, rng):
    P = []
    while len(P) < N:
        t, x = 2*rng.random()-1, 2*rng.random()-1
        if abs(t) + abs(x) <= 1: P.append((t, x))
    P = np.array(sorted(P, key=lambda p: p[0])); T, X = P[:, 0], P[:, 1]
    dt = T[None, :] - T[:, None]; dx = X[None, :] - X[:, None]
    c = (dt > 0) & (dt*dt - dx*dx > 0); inter = c.astype(int) @ c.astype(int)
    link = c & (inter == 0); A = (link | link.T).astype(float); np.fill_diagonal(A, 0)
    s = -np.ones(N, int); cid = 0
    for st in range(N):
        if s[st] >= 0: continue
        q = [st]; s[st] = cid
        while q:
            u = q.pop()
            for w in np.where(A[u] > 0)[0]:
                if s[w] < 0: s[w] = cid; q.append(w)
        cid += 1
    idx = np.where(s == np.argmax(np.bincount(s)))[0]; return A[np.ix_(idx, idx)]

# --- spectra, probe, chord, band split --------------------------------------
def neig(A):
    d = A.sum(1); d[d == 0] = 1; di = 1/np.sqrt(d)
    return np.clip(np.linalg.eigvalsh(np.eye(len(A)) - di[:, None]*A*di[None, :]), 0, None)

def ceig(A):
    d = A.sum(1); return np.clip(np.linalg.eigvalsh(np.diag(d) - A), 0, None)

def ds(ev, sig):
    e = ev[:, None]; E = np.exp(-sig[None, :]*e); return 2*sig*(e*E).sum(0)/E.sum(0)

def chord(ev):
    """D_S/tau at the relaxation-time crossing D_S=2 (tau = sigma * <lambda>_bulk)."""
    bulk = ev[ev > 1e-9].mean(); tt = np.linspace(0.2, 3.5, 12000)
    d = ds(ev, tt/bulk); ix = np.where(d >= 2)[0]
    return 2/tt[ix[0]] if len(ix) else float('nan')

def band(ev):
    """Optimal 1-D two-means split of the nonzero spectrum: p, q, a, b, rho=b/a."""
    nz = np.sort(ev[ev > 1e-9]); best = None
    for i in range(1, len(nz)):
        a = nz[:i].mean(); b = nz[i:].mean()
        w = ((nz[:i]-a)**2).sum() + ((nz[i:]-b)**2).sum()
        if best is None or w < best[0]: best = (w, i, a, b)
    _, i, a, b = best; return i, len(nz)-i, a, b, b/a

if __name__ == "__main__":
    rng = np.random.default_rng(7); _ = cdt_adjacency(24, 24, 0.3, rng)
    Afig = causal(576, rng); nf, cf = neig(Afig), ceig(Afig)
    print("FIGURE realization (cdt pre-roll, causal(576)):")
    print(f"  normalized chord   = {chord(nf):.4f}  (Section V: 1.76)")
    print(f"  combinatorial chord = {chord(cf):.4f}  (Section V: 1.58)")
    print("BAND across N (fresh default_rng(7), causal(N) direct):")
    print(f"  {'N':>5} {'p:q':>12} {'rho':>6} {'norm_chord':>11} {'gapfrac<0.1':>12}")
    for N in [64, 256, 576, 1024, 2025]:
        rng = np.random.default_rng(7); A = causal(N, rng); ev = neig(A)
        p, q, a, b, r = band(ev)
        print(f"  {N:>5} {f'{p}:{q}':>12} {r:>6.2f} {chord(ev):>11.3f} {np.mean(ev <= 0.1):>12.4f}")
