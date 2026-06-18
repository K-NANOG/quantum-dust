/-
The population → empirical bridge (rebuild), machine-checked.

Proposition `prop:cv2` controls the *population* coefficient of variation of a single pairwise
Fubini--Study distance; Theorem `thm:dust` is a deterministic inequality on a *given* list. The
physically content-bearing step is that the C(m,2) **dependent** pairwise distances of one *actual
sample* concentrate — i.e. the *empirical* CV² of the sample vanishes, so the thresholded graph of
a real sample is K_m. This file formalizes exactly that bridge.

The dependence among the pairs is irrelevant: with m fixed, Boole's inequality over the *finite*
set of C(m,2) pairs is all that is needed — no independence, no CLT over a growing index set. Given
the per-pair (marginal) tail `μ{|D_i − c| > ε} ≤ q` (supplied by `BetaMoments.beta_tail`: for the
squared overlap `u ~ Beta(1,n)`, `P(u > sin²ε) = cos^{2n}ε`, the cited marginal law), we conclude:

  * `empirical_collapse` : `μ{ω | ε² < variance(sample ω)} ≤ N · q`  (the sample's CV² collapses);
  * `complete_graph_whp` : `μ{ω | some edge dropped} ≤ N · q`        (the graph is K_m, w.h.p.).

Both → 0 since `N · q = C(m,2)·cos^{2n}ε → 0` for fixed m. Elementary; 0 physics axioms (audited).
The marginal law `u ~ Beta(1,n)` is the one cited input, entering as the hypothesis `htail`.
-/
import Mathlib
import proofs.Concentration

namespace Verified.EmpiricalCollapse

open MeasureTheory Finset

/-- **Boole's inequality over the fixed `N = C(m,2)` pairs.** If each pairwise event `E i` has
probability `≤ q`, the event that *some* pair occurs has probability `≤ N · q`. No independence is
used: the index set is finite, so the union bound suffices. This is the bridge from the per-pair
marginal tail to the empirical collapse of an actual sample. -/
theorem bad_event_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (E : Fin N → Set Ω) (q : ENNReal) (hq : ∀ i, μ (E i) ≤ q) :
    μ (⋃ i, E i) ≤ (N : ENNReal) * q := by
  calc μ (⋃ i, E i) ≤ ∑' i, μ (E i) := measure_iUnion_le E
    _ = ∑ i, μ (E i) := tsum_fintype _
    _ ≤ ∑ _i : Fin N, q := Finset.sum_le_sum (fun i _ => hq i)
    _ = (N : ENNReal) * q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Empirical collapse, with high probability.** Let `D i : Ω → ℝ` be the `N = C(m,2)` pairwise
distances of a random sample, each bounded by `c` (the Fubini--Study distances never exceed `π/2`)
and each with marginal tail `μ{ω | ε < |D i ω − c|} ≤ q`. Then the probability that the *empirical
variance of the actual sample* exceeds `ε²` is at most `N · q`. With `c = π/2`, `q = cos^{2n}ε`
(`beta_tail`), and `N = C(m,2)`, the bound is `C(m,2)·cos^{2n}ε → 0` for fixed `m`: the sample's
spread vanishes. This is the population→empirical step `cor:floor` needs. 0 physics axioms. -/
theorem empirical_collapse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (hN : 0 < N) (D : Fin N → Ω → ℝ) (c ε : ℝ) (hε : 0 ≤ ε)
    (hub : ∀ i ω, D i ω ≤ c) (q : ENNReal) (htail : ∀ i, μ {ω | ε < |D i ω - c|} ≤ q) :
    μ {ω | ε ^ 2 < Verified.variance (fun i => D i ω)} ≤ (N : ENNReal) * q := by
  refine le_trans (measure_mono ?_) (bad_event_le μ (fun i => {ω | ε < |D i ω - c|}) q htail)
  intro ω hω
  rw [Set.mem_iUnion]
  by_contra hcon
  push_neg at hcon
  have hmem : ∀ i, c - ε ≤ D i ω ∧ D i ω ≤ c := by
    intro i
    refine ⟨?_, hub i ω⟩
    have hi : |D i ω - c| ≤ ε := by
      have := hcon i
      simpa [Set.mem_setOf_eq, not_lt] using this
    rw [abs_le] at hi
    linarith [hi.1]
  have hvar : Verified.variance (fun i => D i ω) ≤ ε ^ 2 :=
    Verified.variance_le_sq_of_mem_Icc (fun i => D i ω) c ε hN hε
      (fun i => (hmem i).1) (fun i => (hmem i).2)
  simp only [Set.mem_setOf_eq] at hω
  linarith

/-- **The thresholded graph is `K_m`, with high probability.** With the same per-pair tail and
`ε(1+δ) ≤ cδ`, the probability that *some* edge is dropped (some pairwise distance exceeds the
relative threshold `(1+δ)·mean`) is at most `N · q`. So with probability `≥ 1 − C(m,2)cos^{2n}ε`
the thresholded graph of the actual sample is the complete graph `K_m`. 0 physics axioms. -/
theorem complete_graph_whp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (hN : 0 < N) (D : Fin N → Ω → ℝ) (c ε δ : ℝ) (hδ : 0 < δ)
    (hεδ : ε * (1 + δ) ≤ c * δ) (hub : ∀ i ω, D i ω ≤ c)
    (q : ENNReal) (htail : ∀ i, μ {ω | ε < |D i ω - c|} ≤ q) :
    μ {ω | ∃ i, (1 + δ) * Verified.mean (fun i => D i ω) < D i ω} ≤ (N : ENNReal) * q := by
  refine le_trans (measure_mono ?_) (bad_event_le μ (fun i => {ω | ε < |D i ω - c|}) q htail)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  obtain ⟨i, hi⟩ := hω
  rw [Set.mem_iUnion]
  by_contra hcon
  push_neg at hcon
  have hmem : ∀ j, c - ε ≤ D j ω ∧ D j ω ≤ c := by
    intro j
    refine ⟨?_, hub j ω⟩
    have hj : |D j ω - c| ≤ ε := by
      have := hcon j
      simpa [Set.mem_setOf_eq, not_lt] using this
    rw [abs_le] at hj
    linarith [hj.1]
  have hret := Verified.edges_retained_of_mem_Icc (fun j => D j ω) c ε δ hN hδ hεδ
    (fun j => (hmem j).1) (fun j => (hmem j).2) i
  linarith

end Verified.EmpiricalCollapse
