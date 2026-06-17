#!/usr/bin/env python3
"""Emit the data for the honest trichotomy figure (3 panels). N=576."""
import numpy as np

def cdt_adjacency(N_s, T, p, rng):
    N=N_s*T; A=np.zeros((N,N)); v=lambda t,s:t*N_s+s
    for t in range(T):
        for s in range(N_s):
            A[v(t,s),v(t,(s+1)%N_s)]=1; A[v(t,(s+1)%N_s),v(t,s)]=1
        tn=(t+1)%T
        for s in range(N_s):
            sn=(s+1)%N_s
            A[v(t,s),v(tn,s)]=1; A[v(tn,s),v(t,s)]=1
            if rng.random()<p: A[v(t,sn),v(tn,s)]=1; A[v(tn,s),v(t,sn)]=1
            else: A[v(t,s),v(tn,sn)]=1; A[v(tn,sn),v(t,s)]=1
    np.fill_diagonal(A,0); return np.minimum(A,1.0)

def causal(N,rng):
    P=[]
    while len(P)<N:
        t,x=2*rng.random()-1,2*rng.random()-1
        if abs(t)+abs(x)<=1: P.append((t,x))
    P=np.array(sorted(P,key=lambda p:p[0])); T,X=P[:,0],P[:,1]
    dt=T[None,:]-T[:,None]; dx=X[None,:]-X[:,None]
    c=(dt>0)&(dt*dt-dx*dx>0); inter=c.astype(int)@c.astype(int)
    link=c&(inter==0); A=(link|link.T).astype(float); np.fill_diagonal(A,0)
    s=-np.ones(N,int); cid=0
    for st in range(N):
        if s[st]>=0: continue
        q=[st]; s[st]=cid
        while q:
            u=q.pop()
            for w in np.where(A[u]>0)[0]:
                if s[w]<0: s[w]=cid; q.append(w)
        cid+=1
    idx=np.where(s==np.argmax(np.bincount(s)))[0]; return A[np.ix_(idx,idx)]

def melonic(ni,D,rng):
    edges=[(0,1,c) for c in range(D)]; nx=2
    for _ in range(ni):
        c=rng.integers(0,D); ce=[k for k,e in enumerate(edges) if e[2]==c]
        if not ce: continue
        idx=ce[rng.integers(0,len(ce))]; u,vv,_=edges.pop(idx)
        a,b=nx,nx+1; nx+=2; edges.append((u,a,c)); edges.append((b,vv,c))
        for cp in range(D):
            if cp!=c: edges.append((a,b,cp))
    A=np.zeros((nx,nx))
    for u,vv,_ in edges:
        if u!=vv: A[u,vv]=1; A[vv,u]=1
    return A

def eigs(A):
    d=A.sum(1); d[d==0]=1; di=1/np.sqrt(d)
    return np.clip(np.linalg.eigvalsh(np.eye(len(A))-di[:,None]*A*di[None,:]),0,None)
def ds(ev,sig):
    e=ev[:,None]; E=np.exp(-sig[None,:]*e); return 2*sig*(e*E).sum(0)/E.sum(0)

rng=np.random.default_rng(7); N=576; k=24
E={'cdt':eigs(cdt_adjacency(k,k,0.3,rng)),
   'cau':eigs(causal(N,rng)),
   'mel':eigs(melonic(N//2-1,3,rng)),
   'dust':np.r_[0.0,np.full(N-1,N/(N-1.0))]}
import os; D=os.path.dirname(__file__); out=os.path.join(D,'data')

# panel 1: raw D_S(sigma)
sig=np.logspace(-2,2,90)
with open(os.path.join(out,'fig_raw.csv'),'w') as f:
    f.write("logsig cdt cau mel\n")
    for i,s in enumerate(sig):
        f.write(f"{np.log10(s):.4f} {ds(E['cdt'],np.array([s]))[0]:.4f} {ds(E['cau'],np.array([s]))[0]:.4f} {ds(E['mel'],np.array([s]))[0]:.4f}\n")

# panel 2: integrated density of states near 0  (frac of eigenvalues <= lambda)
with open(os.path.join(out,'fig_idos.csv'),'w') as f:
    f.write("lam cdt cau mel\n")
    grid=np.linspace(0,0.6,60)
    for lam in grid:
        f.write(f"{lam:.4f} {np.mean(E['cdt']<=lam):.4f} {np.mean(E['cau']<=lam):.4f} {np.mean(E['mel']<=lam):.4f}\n")

# panel 3: rescaled to relaxation units tau = sigma*<lambda>_bulk ; dust line 2*tau*g
def bulk(ev): nz=ev[ev>1e-9]; return nz.mean()
tau=np.logspace(-1.3,0.8,90)
with open(os.path.join(out,'fig_rescaled.csv'),'w') as f:
    f.write("tau cdt cau mel dust\n")
    m=N
    for t in tau:
        u=(m-1)*np.exp(-t); dustv=2*t*u/(1+u)
        f.write(f"{t:.5f} {ds(E['cdt'],np.array([t/bulk(E['cdt'])]))[0]:.4f}"
                f" {ds(E['cau'],np.array([t/bulk(E['cau'])]))[0]:.4f}"
                f" {ds(E['mel'],np.array([t/bulk(E['mel'])]))[0]:.4f} {dustv:.4f}\n")
print("wrote fig_raw.csv, fig_idos.csv, fig_rescaled.csv to", out)
