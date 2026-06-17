#!/usr/bin/env python3
"""
THE COLLAPSE TEST — does the causal set lie on the dust's universal curve?

not-(a) (gap) is necessary but NOT sufficient for (b). A gapped non-geometric
expander is the third box. The POSITIVE signature of (b) is: rescaled to
relaxation-time units tau = sigma * <lambda>_bulk, D_S(tau) collapses onto the
dust curve 2*tau*g(tau) with slope 2 at the crossing, convention-free.

Discriminators computed here, per ensemble (K_m dust = reference):
  CV_spec = std/mean of NONZERO eigenvalues : ~0 single cluster (dust) ; O(1) spread
  lam_gap/<lam>                              : ~1 single scale (dust)  ; <<1 gap-below-spread
  slope dD_S/dln sigma at the D_S=2 crossing : ~2 dust crossing ; ~0 plateau ; else spread
  rescaled-curve deviation from 2*t*g(t)     : ~0 on the dust line ; large = off it
Causal set also under the COMBINATORIAL Laplacian: if (b), crossing must be
convention-free (value 2 at one relaxation time).
"""
import numpy as np
import importlib.util, sys
spec = importlib.util.spec_from_file_location("tvg", __file__.replace("collapse_test.py", "tail_vs_gap.py"))
tvg = importlib.util.module_from_spec(spec)
sys.modules["tvg_nomain"] = tvg
# pull only the builders (avoid running tail_vs_gap's module-level analysis)
import types
src = open(__file__.replace("collapse_test.py", "tail_vs_gap.py")).read().split("# ---------- run")[0]
exec(compile(src, "tvg", "exec"), tvg.__dict__)
cdt_adjacency = tvg.cdt_adjacency
causal_set_adjacency = tvg.causal_set_adjacency
melonic_adjacency = tvg.melonic_adjacency

def norm_lap_eigs(A):
    deg = A.sum(1); deg[deg == 0] = 1.0
    di = 1.0/np.sqrt(deg)
    L = np.eye(len(A)) - di[:, None]*A*di[None, :]
    return np.clip(np.linalg.eigvalsh(0.5*(L+L.T)), 0, None)

def comb_lap_eigs(A):
    deg = A.sum(1)
    L = np.diag(deg) - A
    return np.clip(np.linalg.eigvalsh(0.5*(L+L.T)), 0, None)

def ds_at(ev, sig):
    e = ev[:, None]; E = np.exp(-sig[None, :]*e)
    return 2.0*sig*(e*E).sum(0)/E.sum(0)

def dust_curve(tau, m):                      # analytic single-cluster D_S in relax units
    u = (m-1)*np.exp(-tau)
    return 2.0*tau*u/(1.0+u)

def crossing_slope(ev, bulk):
    """slope dD_S/dln sigma at the first D_S=2 up-crossing; and tau* = sigma*·bulk."""
    s = np.logspace(-4, 3, 40000)
    ds = ds_at(ev, s)
    k = np.argmax(ds >= 2.0)
    if k == 0: return np.nan, np.nan
    sc = np.exp(np.interp(2.0, [ds[k-1], ds[k]], [np.log(s[k-1]), np.log(s[k])]))
    h = 1e-3
    d2 = ds_at(ev, np.array([sc*np.exp(h), sc*np.exp(-h)]))
    return (d2[0]-d2[1])/(2*h), sc*bulk

def stats(name, ev, m_ref):
    nz = ev[ev > 1e-9]
    cv = nz.std()/nz.mean()
    bulk = nz.mean(); gap = nz[0]
    frac = np.mean(ev < 0.1)
    slope, taustar = crossing_slope(ev, bulk)
    # rescaled-curve deviation from the dust line over the crossing region tau in [0.3,3]
    taus = np.linspace(0.3, 3.0, 40)
    ds_resc = ds_at(ev, taus/bulk)
    dev = np.max(np.abs(ds_resc - dust_curve(taus, len(ev))))
    print(f"  {name:26} | CV_spec={cv:.3f} | gap/<lam>={gap/bulk:.3f} | frac<0.1={frac:.3f}"
          f" | slope@2={slope:.2f} | tau*(cross)={taustar:.2f} | dev-from-dust={dev:.2f}")
    return cv, slope, dev

N = 576; m_eff = N
print("="*116)
print(f"COLLAPSE TEST at N={N}.  Dust predicts: CV_spec~0, gap/<lam>~1, slope@2~2, tau*~1, dev~0.")
print("="*116)
# reference dust K_m
ev_dust = np.r_[0.0, np.full(m_eff-1, m_eff/(m_eff-1.0))]
stats("K_m DUST (reference)", ev_dust, m_eff)
# the three ensembles (normalized Laplacian)
rng = np.random.default_rng(7)
stats("CDT (normalized L)",   norm_lap_eigs(cdt_adjacency(int(round(N**0.5)), int(round(N**0.5)), 0.3, rng)), m_eff)
A_cs = causal_set_adjacency(N, rng)
stats("CAUSAL SET (norm L)",  norm_lap_eigs(A_cs), len(A_cs))
stats("MELONIC (normalized L)", norm_lap_eigs(melonic_adjacency(N//2-1, 3, rng)), m_eff)

print("\nCONVENTION TEST on the causal set (if (b), crossing is convention-free, value 2, tau*~1):")
stats("CAUSAL SET (norm L)",  norm_lap_eigs(A_cs), len(A_cs))
stats("CAUSAL SET (comb L)",  comb_lap_eigs(A_cs), len(A_cs))

print("\nVERDICT:")
print("  causal set CV_spec~0 & slope@2~2 & dev~0 & convention-free  => (b) DUST, headline as written.")
print("  causal set CV_spec=O(1) or slope@2 far from 2 or dev large  => third box (non-geometric expander), soften.")
