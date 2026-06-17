/-
L2 of the Universal Kinematic Value (rebuild) — the concentration step, machine-checked.

We formalize the genuinely-content-bearing core of "CV² → 0 ⇒ the metric graph → K_m":
the empirical Chebyshev / union bound. For a finite family of pairwise distances, the
count of entries deviating (in squared form) from the mean by at least a threshold is
controlled by the total squared deviation. Taking the threshold (δ·mean)² shows that a
vanishing coefficient of variation forces asymptotic equidistance — the dust / K_m regime.

Elementary finite-sum argument: 0 physics axioms (audited in Verified/AxiomCheck.lean).
The Lévy step (that CV² → 0 actually holds for a given family) is an INPUT, not proved here.
-/
import Mathlib

namespace Verified
open Finset

variable {k : ℕ}

/-- Empirical mean of a finite family of reals. -/
noncomputable def mean (d : Fin k → ℝ) : ℝ := (∑ i, d i) / (k : ℝ)

/-- Empirical variance about the mean. -/
noncomputable def variance (d : Fin k → ℝ) : ℝ :=
  (∑ i, (d i - mean d) ^ 2) / (k : ℝ)

/-- **Empirical Chebyshev / union bound (L2 core).** The number of entries whose squared
deviation from the mean is at least `s`, times `s`, is at most the total squared deviation.
Elementary; 0 physics axioms. -/
theorem count_sqdev_mul_le (d : Fin k → ℝ) (s : ℝ) :
    ((univ.filter (fun i => s ≤ (d i - mean d) ^ 2)).card : ℝ) * s
      ≤ ∑ i, (d i - mean d) ^ 2 := by
  have hconst :
      ((univ.filter (fun i => s ≤ (d i - mean d) ^ 2)).card : ℝ) * s
        = ∑ _i ∈ univ.filter (fun i => s ≤ (d i - mean d) ^ 2), s := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  refine le_trans (Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => sq_nonneg _)

/-- **Chebyshev in variance form.** The count of entries whose squared deviation reaches the
relative threshold `(δ·mean)²`, scaled by that threshold, is at most `k · variance`. Dividing,
the *fraction* of such entries is `≤ (variance / mean²) / δ² = CV² / δ²`, so `CV² → 0` drives the
deviating fraction to 0 (asymptotic equidistance). 0 physics axioms. -/
theorem chebyshev_count (d : Fin k → ℝ) (hk : 0 < k) (δ : ℝ) :
    ((univ.filter (fun i => (δ * mean d) ^ 2 ≤ (d i - mean d) ^ 2)).card : ℝ) * (δ * mean d) ^ 2
      ≤ (k : ℝ) * variance d := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hsum : (k : ℝ) * variance d = ∑ i, (d i - mean d) ^ 2 := by
    unfold variance
    field_simp
  rw [hsum]
  exact count_sqdev_mul_le d _

/-- **Mean of a bounded family lies in the interval.** If every entry lies in `[c-ε, c]`, so does
the empirical mean. -/
theorem mean_mem_Icc (d : Fin k → ℝ) (c ε : ℝ) (hk : 0 < k)
    (hlo : ∀ i, c - ε ≤ d i) (hhi : ∀ i, d i ≤ c) :
    c - ε ≤ mean d ∧ mean d ≤ c := by
  have hk' : (0:ℝ) < (k:ℝ) := Nat.cast_pos.mpr hk
  refine ⟨?_, ?_⟩
  · unfold mean
    rw [le_div_iff₀ hk']
    have h := Finset.sum_le_sum (fun (i : Fin k) (_ : i ∈ Finset.univ) => hlo i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    linarith
  · unfold mean
    rw [div_le_iff₀ hk']
    have h := Finset.sum_le_sum (fun (i : Fin k) (_ : i ∈ Finset.univ) => hhi i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    linarith

/-- **Uniform empirical collapse (variance).** If every pairwise distance lies in `[c-ε, c]` (the
high-probability event supplied by the union bound in `Verified/EmpiricalCollapse.lean`), the
empirical variance is at most `ε²`. With `c = π/2` and `ε → 0` this is the dust: the spread of an
*actual sample* vanishes, not merely the population spread. 0 physics axioms. -/
theorem variance_le_sq_of_mem_Icc (d : Fin k → ℝ) (c ε : ℝ) (hk : 0 < k) (_hε : 0 ≤ ε)
    (hlo : ∀ i, c - ε ≤ d i) (hhi : ∀ i, d i ≤ c) :
    variance d ≤ ε ^ 2 := by
  have hk' : (0:ℝ) < (k:ℝ) := Nat.cast_pos.mpr hk
  obtain ⟨hml, hmh⟩ := mean_mem_Icc d c ε hk hlo hhi
  have hpt : ∀ i, (d i - mean d) ^ 2 ≤ ε ^ 2 := by
    intro i
    have h1 : d i - mean d ≤ ε := by linarith [hhi i, hml]
    have h2 : -ε ≤ d i - mean d := by linarith [hlo i, hmh]
    exact sq_le_sq' h2 h1
  unfold variance
  rw [div_le_iff₀ hk']
  have h := Finset.sum_le_sum (fun (i : Fin k) (_ : i ∈ Finset.univ) => hpt i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- **Empirical coefficient of variation on the good event.** With `ε < c`, the empirical
`CV² = variance/mean²` is at most `ε²/(c-ε)²`, hence `→ 0` as `ε → 0`: the sampled `CV²` collapses,
which is exactly the hypothesis `chebyshev_count`/`thm:dust` consumes. -/
theorem cv_sq_le_of_mem_Icc (d : Fin k → ℝ) (c ε : ℝ) (hk : 0 < k) (hε : 0 ≤ ε) (hεc : ε < c)
    (hlo : ∀ i, c - ε ≤ d i) (hhi : ∀ i, d i ≤ c) :
    variance d / (mean d) ^ 2 ≤ ε ^ 2 / (c - ε) ^ 2 := by
  obtain ⟨hml, _⟩ := mean_mem_Icc d c ε hk hlo hhi
  have hcε : 0 < c - ε := by linarith
  have hmean_pos : 0 < mean d := by linarith
  have hvar : variance d ≤ ε ^ 2 := variance_le_sq_of_mem_Icc d c ε hk hε hlo hhi
  have hden : (c - ε) ^ 2 ≤ (mean d) ^ 2 := by nlinarith [hml, hcε]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hvar (sq_nonneg (c - ε)),
    mul_le_mul_of_nonneg_left hden (sq_nonneg ε)]

/-- **All edges retained: the complete graph.** On the good event, if `ε(1+δ) ≤ cδ`, every pairwise
distance is within the relative threshold `(1+δ)·mean`, so the thresholded graph keeps every edge —
it is the complete graph `K_m`. Together with `variance_le_sq_of_mem_Icc` this is the collapse of an
actual sample to the dust, machine-checked. 0 physics axioms. -/
theorem edges_retained_of_mem_Icc (d : Fin k → ℝ) (c ε δ : ℝ) (hk : 0 < k)
    (hδ : 0 < δ) (hεδ : ε * (1 + δ) ≤ c * δ)
    (hlo : ∀ i, c - ε ≤ d i) (hhi : ∀ i, d i ≤ c) :
    ∀ i, d i ≤ (1 + δ) * mean d := by
  obtain ⟨hml, _⟩ := mean_mem_Icc d c ε hk hlo hhi
  intro i
  have hc : c ≤ (1 + δ) * (c - ε) := by nlinarith [hεδ, hδ]
  calc d i ≤ c := hhi i
    _ ≤ (1 + δ) * (c - ε) := hc
    _ ≤ (1 + δ) * mean d := by nlinarith [hml, hδ]

end Verified
