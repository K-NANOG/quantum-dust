#!/usr/bin/env python3
"""
IS BOX (c) A FIXED POINT, OR A FINITE-SIZE WAY-STATION?

The causal-set link graph sat at: gap (frac(lam<0.1)->0, not (a)) + spread
(CV_spec~0.32, not the dust's single cluster (b)). For "(c) = gapped with
multiple relaxation scales" to be a real third possibility and not (a)/(b)
caught at small N, its membership must be STABLE as N grows:
  CV_spec  must stay O(1)        (a band, not collapsing to the dust's 0)
  frac<0.1 must stay ~0          (a gap, not developing a small-lambda tail => (a))
  slope@2  must stay away from 2 (not drifting onto the dust's crossing => (b))
Tracked against two controls: K_m dust (CV_spec=0 at all N) and CDT (a tail).
"""
import numpy as np

def cdt_adjacency(N_s, T, p_flip, rng):
    N = N_s*T; A = np.zeros((N, N)); v = lambda t, s: t*N_s + s
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

def causal_set_adjacency(N, rng):                       # vectorised transitive reduction
    P = []
    while len(P) < N:
        t, x = 2*rng.random()-1, 2*rng.random()-1
        if abs(t)+abs(x) <= 1.0: P.append((t, x))
    P = np.array(sorted(P, key=lambda p: p[0]))
    T, X = P[:, 0], P[:, 1]
    dt = T[None, :]-T[:, None]; dx = X[None, :]-X[:, None]
    caus = (dt > 0) & (dt*dt - dx*dx > 0)               # i<j future
    inter = caus.astype(np.int32) @ caus.astype(np.int32)
    link = caus & (inter == 0)
    A = (link | link.T).astype(float); np.fill_diagonal(A, 0)
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
    idx = np.where(seen == np.argmax(np.bincount(seen)))[0]
    return A[np.ix_(idx, idx)]

def norm_lap_eigs(A):
    deg = A.sum(1); deg[deg == 0] = 1.0; di = 1/np.sqrt(deg)
    return np.clip(np.linalg.eigvalsh(np.eye(len(A)) - di[:, None]*A*di[None, :]), 0, None)

def ds_at(ev, sig):
    e = ev[:, None]; E = np.exp(-sig[None, :]*e); return 2.0*sig*(e*E).sum(0)/E.sum(0)

def slope_at_2(ev):
    s = np.logspace(-4, 3, 20000); ds = ds_at(ev, s)
    k = np.argmax(ds >= 2.0)
    if k == 0: return np.nan
    sc = np.exp(np.interp(2.0, [ds[k-1], ds[k]], [np.log(s[k-1]), np.log(s[k])]))
    d2 = ds_at(ev, np.array([sc*1.001, sc*0.999])); return (d2[0]-d2[1])/(2*0.001)

def row(ev):
    nz = ev[ev > 1e-9]
    return nz.std()/nz.mean(), nz[0]/nz.mean(), np.mean(ev < 0.1), slope_at_2(ev), ds_at(ev, np.array([1.0]))[0]

print(f"{'N':>5} | {'CV_spec':>22} | {'gap/<lam>':>16} | {'frac<0.1':>14} | {'slope@2':>14} | {'D_S(1)':>8}")
print("-"*96)
for k in [8, 12, 16, 24, 32, 40, 45]:
    N = k*k
    # causal set: 3 trials
    cs = []
    for tr in range(3):
        rng = np.random.default_rng(100*tr + N)
        cs.append(row(norm_lap_eigs(causal_set_adjacency(N, rng))))
    cs = np.array(cs); m = cs.mean(0); sd = cs.std(0)
    # references
    ev_dust = np.r_[0.0, np.full(N-1, N/(N-1.0))]; dcv = row(ev_dust)[0]
    rng = np.random.default_rng(7)
    ccv = row(norm_lap_eigs(cdt_adjacency(k, k, 0.3, rng)))[0]
    print(f"{N:>5} | {m[0]:.3f}±{sd[0]:.3f} (dust {dcv:.2f}, CDT {ccv:.2f}) "
          f"| {m[1]:.3f}±{sd[1]:.3f} | {m[2]:.3f}±{sd[2]:.3f} | {m[3]:.2f}±{sd[3]:.2f} | {m[4]:.3f}")

print("\n(c) STABLE  <=>  CV_spec stays O(1) (not ->0), frac<0.1 stays ~0 (not growing), slope@2 stays <2.")
print("(c) drifts  <=>  CV_spec->0 (=> (b) dust)  OR  frac<0.1 grows w/ tail (=> (a) geometry).")
