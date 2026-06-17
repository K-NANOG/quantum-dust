#!/usr/bin/env python3
"""
THE DICHOTOMY TEST (tail vs gap) on the three QG ensembles.

Forced consequence of how D_S is built:
  (a) genuine geometric dimension  <=>  power-law TAIL in eigenvalue density near 0
                                        <=>  D_S(sigma) holds a PLATEAU (flat window)
  (b) probe artifact (the dust's 2) <=>  spectral GAP near 0
                                        <=>  D_S(sigma) only CROSSES, never plateaus.

We reproduce the repo's normalized-Laplacian constructions (CDT triangulation,
sprinkled causal set, melonic colored-tensor graph), validate D_S(1) against the
published 1.62 / 1.66 / 1.22, then look at the spectrum near 0 and the running D_S.
"""
import numpy as np

# ---------- ensemble constructions (ports of the repo's .jl) ----------------
def cdt_adjacency(N_s, T, p_flip, rng):
    N = N_s * T
    A = np.zeros((N, N))
    v = lambda t, s: t * N_s + s            # 0-indexed t in 0..T-1, s in 0..N_s-1
    for t in range(T):
        for s in range(N_s):                # spatial ring
            sn = (s + 1) % N_s
            A[v(t, s), v(t, sn)] = 1; A[v(t, sn), v(t, s)] = 1
        tn = (t + 1) % T
        for s in range(N_s):                # temporal: vertical + diagonal (flip)
            sn = (s + 1) % N_s
            A[v(t, s), v(tn, s)] = 1; A[v(tn, s), v(t, s)] = 1
            if rng.random() < p_flip:
                A[v(t, sn), v(tn, s)] = 1; A[v(tn, s), v(t, sn)] = 1
            else:
                A[v(t, s), v(tn, sn)] = 1; A[v(tn, sn), v(t, s)] = 1
    np.fill_diagonal(A, 0)
    return np.minimum(A, 1.0)

def causal_set_adjacency(N, rng):
    pts = []
    while len(pts) < N:
        t, x = 2*rng.random()-1, 2*rng.random()-1
        if abs(t) + abs(x) <= 1.0:
            pts.append((t, x))
    pts = np.array(sorted(pts, key=lambda p: p[0]))        # sort by time
    caus = np.zeros((N, N), bool)
    for i in range(N):
        ti, xi = pts[i]
        for j in range(i+1, N):
            dt, dx = pts[j,0]-ti, pts[j,1]-xi
            if dt > 0 and dt*dt - dx*dx > 0:
                caus[i, j] = True
    A = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            if not caus[i, j]:
                continue
            inter = any(caus[i, k] and caus[k, j] for k in range(i+1, j))
            if not inter:
                A[i, j] = 1; A[j, i] = 1
    return largest_component(A)

def largest_component(A):
    N = len(A); seen = -np.ones(N, int); cid = 0
    for s in range(N):
        if seen[s] >= 0: continue
        q = [s]; seen[s] = cid
        while q:
            u = q.pop()
            for w in np.where(A[u] > 0)[0]:
                if seen[w] < 0: seen[w] = cid; q.append(w)
        cid += 1
    best = np.argmax(np.bincount(seen))
    idx = np.where(seen == best)[0]
    return A[np.ix_(idx, idx)]

def melonic_adjacency(n_insertions, D, rng):
    edges = [(0, 1, c) for c in range(D)]      # initial melon
    nxt = 2
    for _ in range(n_insertions):
        c = rng.integers(0, D)
        ce = [k for k, e in enumerate(edges) if e[2] == c]
        if not ce: continue
        idx = ce[rng.integers(0, len(ce))]
        u, vv, _ = edges.pop(idx)
        a, b = nxt, nxt + 1; nxt += 2
        edges.append((u, a, c)); edges.append((b, vv, c))
        for cp in range(D):
            if cp != c: edges.append((a, b, cp))
    N = nxt
    A = np.zeros((N, N))
    for u, vv, _ in edges:
        if u != vv: A[u, vv] = 1; A[vv, u] = 1
    return A

# ---------- spectrum + spectral dimension -----------------------------------
def norm_lap_eigs(A):
    deg = A.sum(1); deg[deg == 0] = 1.0
    di = 1.0 / np.sqrt(deg)
    L = np.eye(len(A)) - di[:, None] * A * di[None, :]
    return np.clip(np.linalg.eigvalsh(0.5*(L+L.T)), 0, None)

def ds_at(ev, sig):
    e = ev[:, None]; E = np.exp(-sig[None, :]*e)
    return 2.0*sig*(e*E).sum(0)/E.sum(0)

SIG = np.logspace(-2, 2, 160)

def analyse(name, build, sizes, target, trials=3):
    print(f"\n{'='*72}\n{name}   (published D_S(1) ~ {target})\n{'='*72}")
    for N in sizes:
        evs, ds1s, lam2s, frac = [], [], [], []
        for tr in range(trials):
            rng = np.random.default_rng(1000*tr + N)
            A = build(N, rng)
            ev = norm_lap_eigs(A)
            evs.append(ev)
            ds1s.append(ds_at(ev, np.array([1.0]))[0])
            nz = ev[ev > 1e-9]
            lam2s.append(nz[0] if len(nz) else np.nan)         # smallest nonzero
            frac.append(np.mean(ev < 0.1))                      # near-0 density
        ev = evs[-1]
        # running D_S over the window; flat-window (plateau) detection
        ds = ds_at(ev, SIG)
        peak = ds.max()
        # widest window with |dD_S/dln sigma| small (plateau) and D_S>0.5
        dlog = np.gradient(ds, np.log(SIG))
        flat = (np.abs(dlog) < 0.25) & (ds > 0.8)
        wflat = flat.sum() * (np.log10(SIG[-1])-np.log10(SIG[0]))/(len(SIG)-1)
        plat_val = np.median(ds[flat]) if flat.any() else np.nan
        print(f"  N={N:>4} (m_eff={len(ev):>4}) | D_S(1)={np.mean(ds1s):.3f}"
              f" | lambda_2={np.nanmean(lam2s):.4f} | frac(lam<0.1)={np.mean(frac):.3f}"
              f" | peak D_S={peak:.2f} | flat-window={wflat:.2f} dec @ D_S={plat_val:.2f}")
    return

# ---------- run -------------------------------------------------------------
print("VALIDATE D_S(1) against published, then read tail-vs-gap from the spectrum.")
analyse("CDT triangulation", lambda N, rng: cdt_adjacency(int(round(N**0.5)), int(round(N**0.5)), 0.3, rng),
        [64, 256, 576], "1.62")
analyse("Causal set (sprinkled M^{1+1})", lambda N, rng: causal_set_adjacency(N, rng),
        [64, 256, 576], "1.66")
analyse("Melonic (rank-3 colored tensor)", lambda N, rng: melonic_adjacency(N//2 - 1, 3, rng),
        [64, 256, 576], "1.22")

print(f"\n{'='*72}\nREAD-OUT KEY")
print("  lambda_2 SHRINKS with N + frac(lam<0.1)>0 + a flat-window  => TAIL  => case (a) genuine dimension")
print("  lambda_2 STAYS bounded + frac~0 + no flat-window (only a peak) => GAP => case (b) probe artifact")
