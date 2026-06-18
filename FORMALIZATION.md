# FORMALIZATION.md — Claims ledger

The trust anchor for *Quantum Dust from the Curse of Dimensionality*. Every paper
label maps here to its exact status. The paper's Formalization paragraph is a
faithful prose rendering of this table; **if you change one, change both in the
same commit.**

## Status vocabulary
- **VERIFIED** — machine-checked in `proofs/`, axiom-clean: `#print axioms`
  reports only `propext`, `Classical.choice`, `Quot.sound`.
- **VERIFIED (conditional)** — machine-checked given a named *explicit hypothesis
  variable* (never an `axiom`); the named input is the only thing assumed.
- **PAGE** — proved on the page, not formalized; reason given (typically a result
  Mathlib does not carry).
- **NUMERICAL** — reproduced by the Part C/D harness; see `RESULTS.md` for the
  claim→value→Δ→pass/fail diff and the regenerating command.
- **CONJECTURE / OPEN** — explicitly not claimed as proved (see §"Conjectures").

## Reproduce the audit
```
# Lean v4.27.0, Mathlib rev 64c76ea (pinned in lean-toolchain / lake-manifest.json)
lake build Verified                      # green: 7888 jobs, no sorry / sorryAx
lake env lean proofs/AxiomCheck.lean   # prints #print axioms for all 36 results
```
Last clean re-elaboration (oleans absent → full re-elaboration of `proofs/`):
**green, 36 results, every one `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.**

---

## Ledger (by paper label)

| Label | Statement (one line) | Status | Location (Lean name) | Dependencies |
|---|---|---|---|---|
| `prop:cv2` (II.1), **polynomial moments** | `E[u]=1/(n+1)`, `E[u²]=2/((n+1)(n+2))` for Beta(1,n) | **VERIFIED** | `Verified.BetaMoments.{integral_u_mul_one_sub_pow, beta_first_moment, integral_u_sq_mul_one_sub_pow, beta_second_moment}` | Mathlib (FTC + explicit antiderivatives) |
| `prop:cv2` (II.1), **coefficient** | `CV² = (4−π)/(π²n) + O(n^{−3/2})` | **PAGE** | — | `E[√u]` (half-integer Beta) + arcsin/Gamma-ratio asymptotic |
| `thm:dust` (II.2) | fraction with `|dᵢ−μ| ≥ δμ` is `≤ CV̂²/δ²` (deterministic, empirical CV̂²) | **VERIFIED** | `Verified.count_sqdev_mul_le`, `Verified.chebyshev_count` | Mathlib |
| `lem:empirical` (II.3), **population→empirical bridge** | per-pair tail `P(u>sin²ε)=cos²ⁿε`; Boole over the `C(m,2)` dependent pairs ⇒ an *actual sample's* `CV̂²→0` and thresholded graph `=K_m` w.h.p. (no independence) | **VERIFIED (conditional)** | `BetaMoments.beta_tail`; `Verified.{mean_mem_Icc, variance_le_sq_of_mem_Icc, cv_sq_le_of_mem_Icc, edges_retained_of_mem_Icc}`; `EmpiricalCollapse.{bad_event_le, empirical_collapse, complete_graph_whp}` | Mathlib + cited marginal `Beta(1,n)` law |
| `thm:two` (III.1) | `K_m` spectrum `{0}∪{m/(m−1)}^{m−1}`; `D_S(K_m,1)→2` | **VERIFIED** | `SpectralDimension.completeGraph_spectralDimension_two`, `…spectralDimension_quantitative` | Mathlib |
| `cor:value` (III.2) | concentration ⇒ `K_m` ⇒ `D_S(1)→2` (the chain) | **VERIFIED (conditional)** | `Verified.UniversalValue.universal_value` | Mathlib + explicit Lévy-concentration hypothesis |
| `thm:relax` (III.3) | `D_S(1/a)=2(m−1)e⁻¹/(1+(m−1)e⁻¹)`, `a` cancels, `→2` | **VERIFIED** | `Verified.RelaxationTime.cluster_relaxation_formula`, `…cluster_spectralDimension_relaxation_two` | Mathlib |
| `prop:nonvac` (IV.1) | witness `μ_k=1, ν_k=1/k` admits no `0<c≤C` | **VERIFIED** | `Verified.Separation.exists_not_spectrallyFaithful` | Mathlib |
| `thm:gap` (IV.2) | `D_S(·,1)→2a`; iff `a→1`; ε-perturbation stability | **VERIFIED** | `Verified.RelaxationTime.cluster_fixedclock_formula`, `…cluster_spectralDimension_fixed_two_a`; `Stability.{exp_neg_mul_lipschitz, heatTrace_perturbation_bound, heatTraceDerivative_perturbation_bound, spectralDimension_stability}` | Mathlib |
| `thm:band` (IV.3) | closed form (eq. band); `L(ρ)`; offset `2e^{−ρ}(ρ−1)/(e⁻¹+e^{−ρ})`; `L(ρ)=2⟺ρ=1` | **VERIFIED** | `Verified.RelaxationTime.{twoCluster_relaxation_formula, bandRelaxationLimit_offset, bandRelaxationLimit_eq_two_iff, twoCluster_relaxation_band_limit}` | Mathlib |
| `thm:transfer` (IV.4), **sandwich half** | density squeeze ⇒ heat-trace squeeze `Θ_G(Ct)≤Θ_M(t)≤Θ_G(ct)` ⇒ exponent `logΘ/logt→−d/2` transfers | **VERIFIED** | `Verified.Transfer.heatTrace_faithful_squeeze`, `Verified.Transfer.exponent_transfer` | Mathlib |
| `thm:transfer` (IV.4), **plateau half — exact power law** | `N(λ)=A·λ^{d/2}` ⇒ `Θ(t)=A·Γ(1+d/2)·t^{−d/2}` ⇒ `D_S(t)=d` exactly ∀`t>0` | **VERIFIED** | `Verified.PowerLaw.{heatTrace_powerLaw, running_dimension_of_closedForm, powerLaw_spectralDimension}` | Mathlib (scaled Gamma integral) |
| `thm:transfer` (IV.4), **plateau half — slowly varying** | `N(λ)=λ^{d/2}·ℓ(λ)` ⇒ `D_S(t)→d` | **PAGE** | — | Karamata Tauberian + monotone-density (Bingham–Goldie–Teugels §1.7.1/§1.7.2), not in Mathlib |
| `prop:mono` (VI.1) | `Σwᵢ≤1 ⇒ minᵢwᵢ ≤ 1/k` (thin-thread half) | **VERIFIED** | `Verified.Monogamy.monogamy_thin_threads` | Mathlib |

All 36 audited Lean names appear above; each is axiom-clean (`[propext, Classical.choice, Quot.sound]`).

---

## PAGE proofs (proved, not formalized — and why)
- **`prop:cv2` coefficient** — the polynomial moments `E[u]=1/(n+1)`, `E[u²]=2/((n+1)(n+2))` are
  now **VERIFIED** (`proofs/BetaMoments.lean`, explicit antiderivatives + FTC; no
  `Real.betaIntegral`, which Mathlib lacks). What remains PAGE: the half-integer moment
  `E[√u]=(√π/2)·Γ(n+1)/Γ(n+3/2)` (needs the Complex→Real bridge for the half-integer Beta) and
  the `(4−π)/(π²n)` arcsin/Gamma-ratio asymptotic that turns the moments into the coefficient.
- **`thm:transfer` plateau half — slowly varying** — the generalization to `N(λ)=λ^{d/2}·ℓ(λ)`
  needs Karamata's Tauberian theorem and the monotone-density theorem (BGT §1.7.1/§1.7.2), not
  in Mathlib. The *exact power-law* case is now **VERIFIED** (`proofs/PowerLaw.lean`); only the
  slowly-varying lift stays on the page.

## NUMERICAL (Part C/D — see `RESULTS.md`)
Section 5 / "What is proved" numerals — fixed-clock readings (CDT `D_S(1)≈1.62`,
causal set `1.79`, melonic `1.22`), plateaus (CDT `2.07` drifting `2.10→2.05`,
melonic `1.28`), causal-set gap fraction `0.016→0`, relaxation slopes
(`2.00`/`1.76`/`1.58`), `592:431` split, `ρ≈1.7`, `L(ρ)≈2.46` — and the
**validation suite** (ring→1, torus→2, Sierpinski→`2ln3/ln5`). Regenerated by the
Part C suite under `experiments/`; `RESULTS.md` carries the diff table, every row reproduced within the per-group tolerances.

## Conjectures / OPEN — never promoted (paper §"What is proved" / Discussion)
- The diffusive 2 **is** the Brownian path's Hausdorff dimension *via a mechanism* —
  a noted resemblance, not a theorem ("a resemblance we note, not a mechanism we claim").
- The UV 2 of any actual QG program **is** the dust artifact — a question posed; the
  paper's own sort shows two of three test structures carry genuine tails.
- Spectral faithfulness (eq. sf) for the real programs, in particular the Lorentzian
  Benincasa–Dowker d'Alembertian vs. the link-graph Laplacian (the link-graph numerics
  are a **proxy**). OPEN.
- Passage from the dust to spacetime (the `CP^n`-via-Dirac-spectral-window convergence).
  OPEN; Rieffel's coadjoint-orbit `CP^n` is affirmative-but-different (Berezin
  quantization on full matrix algebras, not compression of an ambient Dirac operator).
- Fubini–Study equidistance **induces** multipartite monogamy — `prop:mono` proves only
  the elementary thin-thread half; the lift is CONJECTURE.

---
*Frontier (both landed):* **B2** — exact power-law plateau VERIFIED (`proofs/PowerLaw.lean`,
3 theorems); `thm:transfer`'s plateau half moves PAGE→VERIFIED in the power-law case, only the
slowly-varying (Karamata) lift remains page-proved. **B1** — exact polynomial moments `E[u]`,
`E[u²]` VERIFIED (`proofs/BetaMoments.lean`, 4 theorems, explicit antiderivatives + FTC); since
Mathlib's Beta integral is `Complex`-only, the half-integer `E[√u]` and the `(4−π)/(π²n)`
asymptotic stay page-proved. **28 results total, all axiom-clean.** This table and the paper's
Formalization paragraph are updated together with each landing.
