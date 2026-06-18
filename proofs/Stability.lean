/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenan Oggad
-/
import proofs.CompleteGraph  -- (rebuild port of the audited-clean, Mathlib-only Basic.lean)
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Stability Lemma: Eigenvalue Perturbation → Spectral Dimension Stability

This file proves the stability lemma: when eigenvalues of a graph's normalized
Laplacian are ε-close to those of the complete graph K_n, the heat trace and
spectral dimension D_S are correspondingly close.

## Axiom Closure

This file contains zero axioms. Two classical results were originally axiomatized:

* `exp_neg_mul_lipschitz` — **Proved** via the mean value theorem: exp is
  1-Lipschitz on (-∞, 0], so |exp(-ta) - exp(-tb)| ≤ t|a - b| for a, b ≥ 0.

* `weyl_eigenvalue_perturbation` — **Removed** (unused). Downstream theorems
  take eigenvalue closeness `∀ i, |eigG i - eigK i| ≤ ε` as a hypothesis
  directly, making the axiom dead code. Weyl's inequality (1912, Bhatia 1997
  Thm III.2.1) justifies this hypothesis pattern; it is not formalized because
  Mathlib lacks the spectral theorem for finite-dimensional operators.

## Main Results

* `completeGraphEigenvalues_nonneg` - K_n eigenvalues are nonneg
* `weighted_exp_perturbation` - Product perturbation bound from exp Lipschitz
* `heatTrace_perturbation_bound` - |P_G(t) - P_{K_n}(t)| ≤ t·ε
* `heatTraceDerivative_perturbation_bound` - |P'_G(t) - P'_{K_n}(t)| ≤ (M·t+1)·ε
* `spectralDimension_stability` - D_S stability: eigenvalue perturbation → 0
  implies D_S → D_S(K_n)

## The Stability Chain

1. Weyl's inequality: ‖L_G - L_{K_n}‖_op ≤ ε → |λᵢ(G) - λᵢ(K_n)| ≤ ε
   (enters via hypothesis, not axiom; justified by Weyl 1912)
2. Heat trace perturbation: |P_G(t) - P_{K_n}(t)| ≤ t·ε
3. Heat trace derivative perturbation: |P'_G(t) - P'_{K_n}(t)| ≤ (M·t+1)·ε
4. D_S stability: |D_S(G,t) - D_S(K_n,t)| → 0 as ε → 0

This closes the conjunction-to-composition gap in Theorem1.lean. Previously,
the main theorem stated concentration ∧ D_S → 2 as a conjunction. The stability
lemma provides the causal link: approximate K_n eigenvalues (from concentration
via Weyl) IMPLIES approximate D_S = 2.
-/

namespace Stability

open SpectralDimension Filter Topology Real
open scoped BigOperators

/-! ## Remark on Weyl's Inequality

Weyl's eigenvalue perturbation inequality (Weyl 1912, Bhatia 1997 Thm III.2.1)
states |λᵢ(A) - λᵢ(B)| ≤ ‖A - B‖_op for real symmetric matrices. This result
justifies the `h_close : ∀ i, |eigG i - completeGraphEigenvalues n i| ≤ ε`
hypothesis pattern used throughout this file.

Not formalized: Lean 4 / Mathlib lacks the spectral theorem for finite-dimensional
Hermitian operators and the Courant-Fischer min-max characterization. The theorems
below are universally quantified over eigenvalue sequences satisfying the closeness
bound, making them valid for any extraction satisfying Weyl-type bounds. -/

/-- **Exponential Lipschitz Bound** (Proved via MVT)

    The function x ↦ exp(-t·x) is Lipschitz with constant t on [0, ∞):
      |exp(-t·a) - exp(-t·b)| ≤ t · |a - b|  for a, b ≥ 0, t ≥ 0.

    Proof: exp is 1-Lipschitz on (-∞, 0] since |exp'(x)| = exp(x) ≤ 1 for x ≤ 0
    (by the mean value theorem). Applying to -ta, -tb ≤ 0 gives the result. -/
theorem exp_neg_mul_lipschitz (t a b : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |exp (-t * a) - exp (-t * b)| ≤ t * |a - b| := by
  -- exp is 1-Lipschitz on (-∞, 0]: derivative exp(x) ≤ 1 for x ≤ 0
  have h_mvt := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => by
      rw [Set.mem_Iic] at hx
      rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg x)]
      exact (exp_le_exp.mpr hx).trans_eq exp_zero)
    (Set.mem_Iic.mpr (show -t * b ≤ 0 by nlinarith))
    (Set.mem_Iic.mpr (show -t * a ≤ 0 by nlinarith))
  -- h_mvt : ‖exp(-ta) - exp(-tb)‖ ≤ 1 * ‖(-ta) - (-tb)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h_mvt
  calc |exp (-t * a) - exp (-t * b)|
      ≤ |(-t * a) - (-t * b)| := h_mvt
    _ = t * |a - b| := by
        rw [show (-t * a) - (-t * b) = t * (b - a) from by ring,
            abs_mul, abs_of_nonneg ht, abs_sub_comm]

/-! ## Helper Lemmas -/

/-- Complete graph eigenvalues are nonneg: λ₀ = 0 ≥ 0 and λᵢ = n/(n-1) ≥ 0. -/
lemma completeGraphEigenvalues_nonneg (n : ℕ) [NeZero n] (i : Fin n) :
    0 ≤ completeGraphEigenvalues n i := by
  simp only [completeGraphEigenvalues]
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg (Nat.cast_nonneg' n)
    have h_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr h_pos
    linarith

/-- Perturbation bound for weighted exponentials: x·exp(-tx) is locally Lipschitz.

    |a·exp(-ta) - b·exp(-tb)| ≤ (a·t + 1)·|a - b| for a, b ≥ 0, t ≥ 0.

    Proved from the exp Lipschitz bound via the decomposition:
    a·exp(-ta) - b·exp(-tb) = a·(exp(-ta) - exp(-tb)) + (a-b)·exp(-tb) -/
lemma weighted_exp_perturbation (t a b : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a * exp (-t * a) - b * exp (-t * b)| ≤ (a * t + 1) * |a - b| := by
  have h_decomp : a * exp (-t * a) - b * exp (-t * b) =
    a * (exp (-t * a) - exp (-t * b)) + (a - b) * exp (-t * b) := by ring
  rw [h_decomp]
  calc |a * (exp (-t * a) - exp (-t * b)) + (a - b) * exp (-t * b)|
      ≤ |a * (exp (-t * a) - exp (-t * b))| + |(a - b) * exp (-t * b)| := abs_add_le _ _
    _ = a * |exp (-t * a) - exp (-t * b)| + |a - b| * exp (-t * b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (exp_nonneg _)]
    _ ≤ a * (t * |a - b|) + |a - b| * 1 := by
        gcongr
        · exact exp_neg_mul_lipschitz t a b ht ha hb
        · have : exp (-t * b) ≤ exp 0 := by
            apply exp_le_exp.mpr
            nlinarith
          simpa using this
    _ = (a * t + 1) * |a - b| := by ring

/-! ## Heat Trace Perturbation -/

/-- **Heat Trace Perturbation Bound**

    If eigenvalues are pointwise ε-close and nonneg, the heat traces differ
    by at most t·ε:

      |P_G(t) - P_{K_n}(t)| ≤ t · ε

    Proof: Factor out 1/n, apply triangle inequality to the sum, bound each
    term by t·ε using the exp Lipschitz bound, then simplify (1/n)·n·t·ε = t·ε.

    The hypothesis ∀ i, |eigG i - eigK i| ≤ ε follows from Weyl's inequality
    (see remark above) applied to graphs with ε-close Laplacians. -/
theorem heatTrace_perturbation_bound (n : ℕ) [NeZero n]
    (eigG : Fin n → ℝ) (t ε : ℝ) (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (h_nonneg_G : ∀ i, 0 ≤ eigG i)
    (h_close : ∀ i, |eigG i - completeGraphEigenvalues n i| ≤ ε) :
    |heatTrace n eigG t - heatTrace n (completeGraphEigenvalues n) t| ≤ t * ε := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  -- Rewrite as (1/n) * Σ differences
  have h_diff : heatTrace n eigG t - heatTrace n (completeGraphEigenvalues n) t =
      (1 / ↑n : ℝ) * ∑ i : Fin n,
        (exp (-t * eigG i) - exp (-t * completeGraphEigenvalues n i)) := by
    unfold heatTrace
    rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [h_diff, abs_mul, abs_of_nonneg (div_nonneg one_pos.le hn_pos.le)]
  -- Bound: (1/n) * |Σ diffs| ≤ (1/n) * Σ |diffs| ≤ (1/n) * n * tε = tε
  calc (1 / ↑n : ℝ) * |∑ i : Fin n,
        (exp (-t * eigG i) - exp (-t * completeGraphEigenvalues n i))|
      ≤ (1 / ↑n) * ∑ i : Fin n,
          |exp (-t * eigG i) - exp (-t * completeGraphEigenvalues n i)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / ↑n) * ∑ i : Fin n, (t * ε) := by
        gcongr with i _
        calc |exp (-t * eigG i) - exp (-t * completeGraphEigenvalues n i)|
            ≤ t * |eigG i - completeGraphEigenvalues n i| :=
              exp_neg_mul_lipschitz t (eigG i) (completeGraphEigenvalues n i)
                ht (h_nonneg_G i) (completeGraphEigenvalues_nonneg n i)
          _ ≤ t * ε := by gcongr; exact h_close i
    _ = t * ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **Heat Trace Derivative Perturbation Bound**

    If eigenvalues are pointwise ε-close, nonneg, and bounded above by M,
    the heat trace derivatives differ by at most (M·t + 1)·ε:

      |P'_G(t) - P'_{K_n}(t)| ≤ (M · t + 1) · ε

    Proof: Factor out 1/n, apply triangle inequality, bound each term using
    the weighted exp perturbation lemma, then simplify. -/
theorem heatTraceDerivative_perturbation_bound (n : ℕ) [NeZero n]
    (eigG : Fin n → ℝ) (t ε M : ℝ) (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (h_nonneg_G : ∀ i, 0 ≤ eigG i)
    (h_close : ∀ i, |eigG i - completeGraphEigenvalues n i| ≤ ε)
    (h_bound : ∀ i, eigG i ≤ M) (hM : 0 ≤ M) :
    |heatTraceDerivative n eigG t - heatTraceDerivative n (completeGraphEigenvalues n) t| ≤
    (M * t + 1) * ε := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  -- Rewrite as (1/n) * Σ differences (the -(1/n) factors cancel in the difference)
  have h_diff : heatTraceDerivative n eigG t - heatTraceDerivative n (completeGraphEigenvalues n) t =
      -(1 / ↑n : ℝ) * ∑ i : Fin n,
        (eigG i * exp (-t * eigG i) - completeGraphEigenvalues n i * exp (-t * completeGraphEigenvalues n i)) := by
    unfold heatTraceDerivative
    rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [h_diff, abs_mul, abs_neg, abs_of_nonneg (div_nonneg one_pos.le hn_pos.le)]
  calc (1 / ↑n : ℝ) * |∑ i : Fin n,
        (eigG i * exp (-t * eigG i) - completeGraphEigenvalues n i * exp (-t * completeGraphEigenvalues n i))|
      ≤ (1 / ↑n) * ∑ i : Fin n,
          |eigG i * exp (-t * eigG i) - completeGraphEigenvalues n i * exp (-t * completeGraphEigenvalues n i)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / ↑n) * ∑ i : Fin n, ((M * t + 1) * ε) := by
        gcongr with i _
        calc |eigG i * exp (-t * eigG i) - completeGraphEigenvalues n i * exp (-t * completeGraphEigenvalues n i)|
            ≤ (eigG i * t + 1) * |eigG i - completeGraphEigenvalues n i| :=
              weighted_exp_perturbation t (eigG i) (completeGraphEigenvalues n i)
                ht (h_nonneg_G i) (completeGraphEigenvalues_nonneg n i)
          _ ≤ (M * t + 1) * |eigG i - completeGraphEigenvalues n i| := by
              gcongr
              exact h_bound i
          _ ≤ (M * t + 1) * ε := by
              gcongr
              exact h_close i
    _ = (M * t + 1) * ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-! ## Spectral Dimension Stability -/

/-- **Spectral Dimension Stability** (Qualitative)

    For fixed n (with P_{K_n}(t) ≠ 0) and t > 0, as eigenvalue perturbation
    ε → 0, the spectral dimension D_S(G, t) → D_S(K_n, t).

    This is the key composition result: concentration of measure forces
    eigenvalues to be ε-close to K_n (via Weyl), and this theorem shows
    that ε-close eigenvalues yield close spectral dimensions. Together,
    they close the conjunction-to-composition gap in Theorem 1.

    The proof uses the quantitative heat trace and derivative perturbation
    bounds to show P_G → P_K and P'_G → P'_K, then concludes via the
    quotient limit theorem (Tendsto.div). -/
theorem spectralDimension_stability (n : ℕ) [NeZero n] (hn : 1 < n) (t : ℝ) (ht : 0 < t)
    (h_Pt_ne : heatTrace n (completeGraphEigenvalues n) t ≠ 0)
    -- Sequence of eigenvalue perturbations approaching K_n
    (eigSeq : ℕ → Fin n → ℝ) (epsSeq : ℕ → ℝ)
    (h_eps_pos : ∀ k, 0 ≤ epsSeq k)
    (h_eps_vanish : Tendsto epsSeq atTop (nhds 0))
    (h_nonneg : ∀ k i, 0 ≤ eigSeq k i)
    (h_close : ∀ k i, |eigSeq k i - completeGraphEigenvalues n i| ≤ epsSeq k) :
    Tendsto (fun k => runningSpectralDimension n (eigSeq k) t) atTop
      (nhds (runningSpectralDimension n (completeGraphEigenvalues n) t)) := by
  -- Step 1: Heat trace convergence P_G(k) → P_K
  have h_P_bound : ∀ k, |heatTrace n (eigSeq k) t -
      heatTrace n (completeGraphEigenvalues n) t| ≤ t * epsSeq k :=
    fun k => heatTrace_perturbation_bound n (eigSeq k) t (epsSeq k) ht.le (h_eps_pos k)
      (h_nonneg k) (h_close k)
  have h_P_diff_zero : Tendsto (fun k => heatTrace n (eigSeq k) t -
      heatTrace n (completeGraphEigenvalues n) t) atTop (nhds 0) := by
    have h_bound_tend : Tendsto (fun k => t * epsSeq k) atTop (nhds 0) := by
      have := h_eps_vanish.const_mul t
      simp only [mul_zero] at this
      exact this
    rw [Metric.tendsto_atTop] at h_bound_tend ⊢
    intro δ hδ
    obtain ⟨N, hN⟩ := h_bound_tend δ hδ
    exact ⟨N, fun k hk => by
      calc dist (heatTrace n (eigSeq k) t - heatTrace n (completeGraphEigenvalues n) t) 0
          = |heatTrace n (eigSeq k) t - heatTrace n (completeGraphEigenvalues n) t| := by
            rw [Real.dist_eq, sub_zero]
        _ ≤ t * epsSeq k := h_P_bound k
        _ ≤ |t * epsSeq k| := le_abs_self _
        _ = dist (t * epsSeq k) 0 := by rw [Real.dist_eq, sub_zero]
        _ < δ := hN k hk⟩
  have h_P_tend : Tendsto (fun k => heatTrace n (eigSeq k) t) atTop
      (nhds (heatTrace n (completeGraphEigenvalues n) t)) := by
    have h_const : Tendsto (fun _ : ℕ => heatTrace n (completeGraphEigenvalues n) t)
        atTop (nhds (heatTrace n (completeGraphEigenvalues n) t)) := tendsto_const_nhds
    have := h_P_diff_zero.add h_const
    simp only [zero_add] at this
    exact this.congr (fun k => by ring)
  -- Step 2: Heat trace derivative convergence P'_G(k) → P'_K
  -- Eventually epsSeq k < 1, giving eigenvalue bound M = n/(n-1) + 1
  have h_ev_small : ∀ᶠ k in atTop, epsSeq k < 1 :=
    h_eps_vanish.eventually (Iio_mem_nhds one_pos)
  -- Define M as eigenvalue upper bound
  set boundM : ℝ := (↑n : ℝ) / ((↑n : ℝ) - 1) + 1 with boundM_def
  have h_M_nonneg : 0 ≤ boundM := by
    rw [boundM_def]
    have h_n_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
    have h_denom : (0 : ℝ) < (↑n : ℝ) - 1 := by
      have : (1 : ℝ) < ↑n := Nat.one_lt_cast.mpr hn
      linarith
    linarith [div_nonneg h_n_pos.le h_denom.le]
  have h_P'_bound : ∀ᶠ k in atTop, |heatTraceDerivative n (eigSeq k) t -
      heatTraceDerivative n (completeGraphEigenvalues n) t| ≤
      (boundM * t + 1) * epsSeq k := by
    filter_upwards [h_ev_small] with k hk_small
    have h_bd : ∀ i, eigSeq k i ≤ boundM := by
      intro i
      have h_abs : eigSeq k i - completeGraphEigenvalues n i ≤ epsSeq k :=
        (abs_le.mp (h_close k i)).2
      have h_K_bound : completeGraphEigenvalues n i ≤ (↑n : ℝ) / ((↑n : ℝ) - 1) := by
        simp only [completeGraphEigenvalues]
        split_ifs with h
        · apply div_nonneg (Nat.cast_nonneg' n)
          have : (1 : ℝ) ≤ (↑n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
          linarith
        · exact le_refl _
      linarith
    exact heatTraceDerivative_perturbation_bound n (eigSeq k) t (epsSeq k) boundM ht.le (h_eps_pos k)
      (h_nonneg k) (h_close k) h_bd h_M_nonneg
  have h_P'_diff_zero : Tendsto (fun k => heatTraceDerivative n (eigSeq k) t -
      heatTraceDerivative n (completeGraphEigenvalues n) t) atTop (nhds 0) := by
    have h_bound_tend : Tendsto (fun k => (boundM * t + 1) * epsSeq k) atTop (nhds 0) := by
      have := h_eps_vanish.const_mul (boundM * t + 1)
      simp only [mul_zero] at this
      exact this
    rw [Metric.tendsto_atTop] at h_bound_tend ⊢
    intro δ hδ
    obtain ⟨N, hN⟩ := h_bound_tend δ hδ
    have h_ev := h_P'_bound
    rw [Filter.eventually_atTop] at h_ev
    obtain ⟨N', hN'⟩ := h_ev
    exact ⟨max N N', fun k hk => by
      have hk_N : N ≤ k := le_of_max_le_left hk
      have hk_N' : N' ≤ k := le_of_max_le_right hk
      calc dist (heatTraceDerivative n (eigSeq k) t -
              heatTraceDerivative n (completeGraphEigenvalues n) t) 0
          = |heatTraceDerivative n (eigSeq k) t -
              heatTraceDerivative n (completeGraphEigenvalues n) t| := by
            rw [Real.dist_eq, sub_zero]
        _ ≤ (boundM * t + 1) * epsSeq k := hN' k hk_N'
        _ ≤ |(boundM * t + 1) * epsSeq k| := le_abs_self _
        _ = dist ((boundM * t + 1) * epsSeq k) 0 := by rw [Real.dist_eq, sub_zero]
        _ < δ := hN k hk_N⟩
  have h_P'_tend : Tendsto (fun k => heatTraceDerivative n (eigSeq k) t) atTop
      (nhds (heatTraceDerivative n (completeGraphEigenvalues n) t)) := by
    have h_const' : Tendsto (fun _ : ℕ => heatTraceDerivative n (completeGraphEigenvalues n) t)
        atTop (nhds (heatTraceDerivative n (completeGraphEigenvalues n) t)) := tendsto_const_nhds
    have := h_P'_diff_zero.add h_const'
    simp only [zero_add] at this
    exact this.congr (fun k => by ring)
  -- Step 3: D_S = -2t · P'/P → -2t · P'_K/P_K = D_S(K_n) by Tendsto.div
  unfold runningSpectralDimension
  apply Tendsto.div
  · exact h_P'_tend.const_mul (-2 * t)
  · exact h_P_tend
  · exact h_Pt_ne

end Stability
