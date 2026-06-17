#!/usr/bin/env python3
"""
THE FIREWALL FORK: do the finite link-graph plateaus drift toward the rigorous
DJW continuum spectral dimensions, or sit stably off them?

This is NOT a faithfulness pursuit. It is the scope-decider that licenses the one
true sentence each §5 panel earns:
  - CDT continuum d_s = 2     (DJW, causal triangulations -> trees)
  - melonic continuum d_s=4/3 (Gurau: melons ARE branched polymers; DJW trees)
We measure the finite normalized-Laplacian plateau per N and read the DRIFT:
  - CDT plateau 2.099 (N=256) -> 2.052 (N=2025) : drift toward 2 -> report as observed
  - melonic plateau 1.303 -> 1.290              : stable, ~4% below 4/3, NOT drifting
    => the link-graph proxy is NOT shown faithful for melonic (a scope finding
       about the PROXY, not a dent in the instrument, which reads bulk d_s).

Same instrument as tail_vs_gap.py / calibration.py (validated in Stage B).

Run:
  PYTHONPATH=<nix numpy> <nix python3.13> experiments/melonic_cdt_drift.py
"""
import numpy as np

# ---------- constructions (ports of the repo's .jl, == tail_vs_gap.py) ------
def cdt_adjacency(N_s, T, p_flip, rng):
    N = N_s * T; A = np.zeros((N, N)); v = lambda t, s: t * N_s + s
    for t in range(T):
        for s in range(N_s):
            A[v(t, s), v(t, (s+1) % N_s)] = 1; A[v(t, (s+1) % N_s), v(t, s)] = 1
        tn = (t+1) % T
        for s in range(N_s):
            sn = (s+1) % N_s
            A[v(t, s), v(tn, s)] = 1; A[v(tn, s), v(t, s)] = 1
            if rng.random() < p_flip:
                A[v(t, sn), v(tn, s)] = 1; A[v(tn, s), v(t, sn)] = 1
            else:
                A[v(t, s), v(tn, sn)] = 1; A[v(tn, sn), v(t, s)] = 1
    np.fill_diagonal(A, 0); return np.minimum(A, 1.0)

def melonic_adjacency(n_insertions, D, rng):
    edges = [(0, 1, c) for c in range(D)]; nxt = 2
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
    N = nxt; A = np.zeros((N, N))
    for u, vv, _ in edges:
        if u != vv: A[u, vv] = 1; A[vv, u] = 1
    return A

# ---------- instrument (validated Stage B) ----------------------------------
def norm_lap_eigs(A):
    deg = A.sum(1); deg[deg == 0] = 1.0; di = 1.0/np.sqrt(deg)
    L = np.eye(len(A)) - di[:, None]*A*di[None, :]
    return np.clip(np.linalg.eigvalsh(0.5*(L+L.T)), 0, None)

def ds_at(ev, sig):
    e = ev[:, None]; E = np.exp(-sig[None, :]*e); return 2.0*sig*(e*E).sum(0)/E.sum(0)

SIG = np.logspace(-2, 2, 160)
def plateau(ev):
    ds = ds_at(ev, SIG); dlog = np.gradient(ds, np.log(SIG))
    flat = (np.abs(dlog) < 0.25) & (ds > 0.8)
    val = np.median(ds[flat]) if flat.any() else np.nan
    width = flat.sum() * (np.log10(SIG[-1])-np.log10(SIG[0]))/(len(SIG)-1)
    return val, width

# ---------- run the drift ---------------------------------------------------
def drift(name, build, sizes, target, trials=3):
    print(f"\n{name}  (DJW continuum d_s = {target})")
    print(f"  {'N_target':>8} | {'m_eff':>6} | {'plateau D_S':>18} | {'flat dec':>8} | {'gap to target':>13}")
    vals = []
    for N in sizes:
        ps, ws, ms = [], [], []
        for tr in range(trials):
            rng = np.random.default_rng(1000*tr + N)
            A = build(N, rng); ev = norm_lap_eigs(A)
            v, w = plateau(ev); ps.append(v); ws.append(w); ms.append(len(ev))
        mp, sp = np.nanmean(ps), np.nanstd(ps)
        print(f"  {N:>8} | {int(np.mean(ms)):>6} | {mp:>10.3f} ± {sp:<5.3f} | {np.mean(ws):>8.2f} | {mp-target:>+13.3f}")
        vals.append((N, mp))
    # drift verdict
    first, last = vals[0][1], vals[-1][1]
    d = last - first
    toward = "TOWARD" if abs(last-target) < abs(first-target) else "AWAY FROM / STALLED off"
    print(f"  drift over N: {first:.3f} -> {last:.3f}  (Δ={d:+.3f}); plateau moves {toward} the DJW value {target}")
    return vals

print("FIREWALL FORK — finite plateau vs rigorous DJW continuum d_s")
drift("CDT triangulation", lambda N, rng: cdt_adjacency(int(round(N**0.5)), int(round(N**0.5)), 0.3, rng),
      [256, 576, 1024, 1600, 2025], 2.0)
drift("Melonic (rank-3 colored tensor)", lambda N, rng: melonic_adjacency(N//2 - 1, 3, rng),
      [256, 576, 1024, 1600, 2025], 4.0/3.0)

print("\n" + "="*78)
print("FIREWALL READ-OUT (the one true sentence per panel):")
print("  CDT     : if plateau keeps drifting toward 2 -> report 'drift observed toward")
print("            the DJW value 2', NOT a convergence proof (a few N is not a theorem).")
print("  Melonic : if plateau stays ~1.28 (no drift to 4/3=1.333) -> the finite link-graph")
print("            Laplacian is NOT shown faithful to the continuum melonic d_s. A scope")
print("            finding about the PROXY; the instrument (bulk d_s) is untouched.")
