/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenan Oggad
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Spectral Dimension: Basic Definitions

This file defines the spectral dimension of a graph via its Laplacian eigenvalues
and the heat trace.

## Main Definitions

* `heatTrace` - The trace of the heat kernel: P(t) = (1/n) Σᵢ exp(-t λᵢ)
* `runningSpectralDimension` - D_S = -2 · t · P'(t)/P(t)
* `completeGraphEigenvalues` - Eigenvalues of K_n: 0 and n/(n-1)

## Main Results

* `completeGraph_spectralDimension_two` - K_n has D_S(1) → 2 as n → ∞

## Computational Verification

All limit theorems in this file have been verified computationally in Julia
experiments (see experiments/theorem_proof.jl). The formal proofs use
standard Mathlib lemmas for limits.
-/

namespace SpectralDimension

open scoped BigOperators
open Filter Topology Real

variable (n : ℕ) [hn : NeZero n]

/-- The heat trace for a sequence of eigenvalues.
    P(t) = (1/n) Σᵢ exp(-t λᵢ) -/
noncomputable def heatTrace (eigenvalues : Fin n → ℝ) (t : ℝ) : ℝ :=
  (1 / n : ℝ) * ∑ i, Real.exp (-t * eigenvalues i)

/-- The derivative of the heat trace with respect to t.
    dP/dt = -(1/n) Σᵢ λᵢ exp(-t λᵢ) -/
noncomputable def heatTraceDerivative (eigenvalues : Fin n → ℝ) (t : ℝ) : ℝ :=
  -(1 / n : ℝ) * ∑ i, eigenvalues i * Real.exp (-t * eigenvalues i)

/-- The running spectral dimension at time t.
    D_S(t) = -2 · t · P'(t)/P(t) -/
noncomputable def runningSpectralDimension (eigenvalues : Fin n → ℝ) (t : ℝ) : ℝ :=
  -2 * t * (heatTraceDerivative n eigenvalues t) / (heatTrace n eigenvalues t)

/-- Eigenvalues of the normalized Laplacian of the complete graph K_n.
    λ₁ = 0, λ₂ = ... = λₙ = n/(n-1) -/
noncomputable def completeGraphEigenvalues : Fin n → ℝ :=
  fun i => if i = 0 then 0 else n / (n - 1 : ℝ)

/-- The heat trace of the complete graph K_n. -/
noncomputable def completeGraphHeatTrace (t : ℝ) : ℝ :=
  heatTrace n (completeGraphEigenvalues n) t

/-- The sum of exp(-t λᵢ) splits into the zero eigenvalue term and the rest.

    For K_n: λ₀ = 0 (gives exp(0) = 1), and λᵢ = n/(n-1) for i > 0 (n-1 terms).
    So the sum equals 1 + (n-1) · exp(-t·n/(n-1)). -/
lemma eigenvalue_sum_split (hn' : 1 < n) (t : ℝ) :
    ∑ i : Fin n, Real.exp (-t * completeGraphEigenvalues n i) =
    1 + (n - 1 : ℝ) * Real.exp (-t * n / (n - 1 : ℝ)) := by
  -- Rewrite using eigenvalue definition
  simp only [completeGraphEigenvalues]
  -- Note: -t * n / (n - 1) means (-t * n) / (n - 1), same as -t * (n / (n - 1))
  have h_eq_exp : ∀ i : Fin n, i ≠ 0 →
      Real.exp (-t * if i = 0 then 0 else (n : ℝ) / ((n : ℝ) - 1)) =
      Real.exp (-t * (n : ℝ) / ((n : ℝ) - 1)) := by
    intro i hi
    simp only [hi, ↓reduceIte, mul_div_assoc]
  -- Split the sum: isolate i = 0 from i ≠ 0
  rw [← Finset.insert_erase (Finset.mem_univ (0 : Fin n))]
  rw [Finset.sum_insert (by simp [Finset.mem_erase])]
  -- The i = 0 term gives exp(0) = 1
  simp only [↓reduceIte, mul_zero, Real.exp_zero]
  congr 1
  -- All remaining terms (i ≠ 0) have the same value
  have h_same : ∀ i ∈ Finset.univ.erase (0 : Fin n),
      Real.exp (-t * if i = 0 then 0 else (n : ℝ) / ((n : ℝ) - 1)) =
      Real.exp (-t * (n : ℝ) / ((n : ℝ) - 1)) := by
    intro i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hi
    simp only [hi, ↓reduceIte, mul_div_assoc]
  rw [Finset.sum_congr rfl h_same]
  -- The sum of n-1 constant terms equals (n-1) * term
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Card of erased set = n - 1
  congr 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin n))]
  rw [Finset.card_univ, Fintype.card_fin]
  simp only [Nat.cast_sub (Nat.one_le_of_lt hn'), Nat.cast_one]

/-- Explicit formula for the complete graph heat trace:
    P(t) = (1/n)[1 + (n-1)exp(-tn/(n-1))]

    The sum splits as: exp(0) + Σᵢ≠₀ exp(-t·n/(n-1))
    = 1 + (n-1)·exp(-t·n/(n-1)) -/
theorem completeGraph_heatTrace_formula (hn' : 1 < n) (t : ℝ) :
    completeGraphHeatTrace n t =
    (1 / n : ℝ) * (1 + (n - 1 : ℝ) * Real.exp (-t * n / (n - 1 : ℝ))) := by
  unfold completeGraphHeatTrace heatTrace
  congr 1
  exact eigenvalue_sum_split n hn' t

/-!
## Limit Theorems

The key insight is that as n → ∞:
- (n-1)/n → 1 (coefficient of exponential)
- n/(n-1) → 1 (exponent denominator)
- 1/n → 0 (first term contribution vanishes)

So P(t) → 0·1 + 1·exp(-t·1) = exp(-t).
-/

/-- Helper: n/(n-1) → 1 as n → ∞ -/
lemma ratio_limit : Tendsto (fun m : ℕ => (m : ℝ) / (m - 1 : ℝ)) atTop (𝓝 1) := by
  have h : (fun m : ℕ => (1 : ℝ) + 1 / (m - 1 : ℝ)) =ᶠ[atTop] (fun m => (m : ℝ) / (m - 1 : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm' : 1 < (m : ℝ) := Nat.one_lt_cast.mpr hm
    have hne : (m : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hne]
    ring
  apply Tendsto.congr' h
  have h_sum : Tendsto (fun m : ℕ => (1 : ℝ) + 1 / (m - 1 : ℝ)) atTop (𝓝 (1 + 0)) := by
    apply Tendsto.add tendsto_const_nhds
    apply Tendsto.div_atTop tendsto_const_nhds
    -- Show (m : ℝ) - 1 → ∞ as m → ∞
    rw [tendsto_atTop_atTop]
    intro b
    use ⌈b + 2⌉₊
    intro m hm
    have hm_cast : (⌈b + 2⌉₊ : ℝ) ≤ m := Nat.cast_le.mpr hm
    have h1 : b + 2 ≤ ⌈b + 2⌉₊ := Nat.le_ceil (b + 2)
    linarith
  simp only [add_zero] at h_sum
  exact h_sum

/-- Helper: (n-1)/n → 1 as n → ∞ -/
lemma ratio_limit' : Tendsto (fun m : ℕ => (m - 1 : ℝ) / (m : ℝ)) atTop (𝓝 1) := by
  have h : (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ)) =ᶠ[atTop] (fun m => (m - 1 : ℝ) / (m : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hne : (m : ℝ) ≠ 0 := by linarith
    field_simp [hne]
  apply Tendsto.congr' h
  have h_diff : Tendsto (fun m : ℕ => (1 : ℝ) - 1 / (m : ℝ)) atTop (𝓝 (1 - 0)) := by
    apply Tendsto.sub tendsto_const_nhds
    exact tendsto_one_div_atTop_nhds_zero_nat
  simp only [sub_zero] at h_diff
  exact h_diff

/-- In the limit n → ∞, the complete graph heat trace approaches exp(-t).

    From the formula: P(t) = (1/n)[1 + (n-1)exp(-tn/(n-1))]
    Rewrite as: P(t) = 1/n + ((n-1)/n)·exp(-t·n/(n-1))

    As n → ∞:
    - 1/n → 0
    - (n-1)/n → 1
    - n/(n-1) → 1, so exp(-t·n/(n-1)) → exp(-t)

    Therefore P(t) → 0 + 1·exp(-t) = exp(-t). -/
theorem completeGraph_heatTrace_limit (t : ℝ) (_ht : 0 < t) :
    Tendsto (fun m : ℕ =>
      if hm : 0 < m then
        have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        completeGraphHeatTrace m t
      else 0)
    atTop (𝓝 (Real.exp (-t))) := by
  -- For m > 1, use the explicit formula and take limits
  have h_formula : (fun m : ℕ => (1 / m : ℝ) + ((m - 1 : ℝ) / m) * Real.exp (-t * m / (m - 1 : ℝ))) =ᶠ[atTop]
      (fun m => if hm : 0 < m then
        have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        completeGraphHeatTrace m t
      else 0) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm_pos : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
    simp only [dif_pos hm_pos]
    have _inst : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
    rw [completeGraph_heatTrace_formula m hm t]
    ring
  apply Tendsto.congr' h_formula
  -- Now prove the limit of the explicit expression
  -- Limit = 0 + 1 · exp(-t) = exp(-t)
  -- 1/m → 0
  have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have h := @tendsto_one_div_atTop_nhds_zero_nat ℝ _ _
    convert h using 1
  -- exp(-t·m/(m-1)) → exp(-t)
  have h_arg : Tendsto (fun m : ℕ => -t * (m : ℝ) / ((m : ℝ) - 1)) atTop (𝓝 (-t)) := by
    have h_ratio : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) - 1)) atTop (𝓝 1) := ratio_limit
    have h_mul : Tendsto (fun m : ℕ => -t * ((m : ℝ) / ((m : ℝ) - 1))) atTop (𝓝 (-t * 1)) :=
      Tendsto.const_mul (-t) h_ratio
    simp only [mul_one] at h_mul
    convert h_mul using 1
    ext m
    ring
  have h_exp : Tendsto (fun m : ℕ => Real.exp (-t * (m : ℝ) / ((m : ℝ) - 1))) atTop (𝓝 (Real.exp (-t))) :=
    (Real.continuous_exp.tendsto (-t)).comp h_arg
  -- ((m-1)/m) · exp(...) → 1 · exp(-t)
  have h_prod : Tendsto (fun m : ℕ => ((m : ℝ) - 1) / (m : ℝ) * Real.exp (-t * (m : ℝ) / ((m : ℝ) - 1)))
      atTop (𝓝 (1 * Real.exp (-t))) :=
    Tendsto.mul ratio_limit' h_exp
  -- Sum: 1/m + (...) → 0 + 1·exp(-t)
  have h_sum : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ) + ((m : ℝ) - 1) / (m : ℝ) * Real.exp (-t * (m : ℝ) / ((m : ℝ) - 1)))
      atTop (𝓝 ((0 : ℝ) + 1 * Real.exp (-t))) :=
    Tendsto.add h1 h_prod
  simp only [zero_add, one_mul] at h_sum
  exact h_sum

/-- The sum of λᵢ * exp(-t λᵢ) for complete graph eigenvalues.

    For K_n: λ₀ = 0 (contributes 0), λᵢ = n/(n-1) for i > 0.
    Sum = 0 + (n-1) · (n/(n-1)) · exp(-t·n/(n-1)) = n · exp(-t·n/(n-1)). -/
lemma eigenvalue_weighted_sum_split (hn' : 1 < n) (t : ℝ) :
    ∑ i : Fin n, completeGraphEigenvalues n i * Real.exp (-t * completeGraphEigenvalues n i) =
    (n : ℝ) * Real.exp (-t * n / (n - 1 : ℝ)) := by
  simp only [completeGraphEigenvalues]
  -- Split the sum: isolate i = 0 from i ≠ 0
  rw [← Finset.insert_erase (Finset.mem_univ (0 : Fin n))]
  rw [Finset.sum_insert (by simp [Finset.mem_erase])]
  -- The i = 0 term: 0 * exp(0) = 0
  simp only [↓reduceIte, mul_zero, Real.exp_zero, mul_one, zero_add]
  -- All remaining terms (i ≠ 0) have the same value
  have h_same : ∀ i ∈ Finset.univ.erase (0 : Fin n),
      (if i = 0 then 0 else (n : ℝ) / ((n : ℝ) - 1)) *
      Real.exp (-t * if i = 0 then 0 else (n : ℝ) / ((n : ℝ) - 1)) =
      (n : ℝ) / ((n : ℝ) - 1) * Real.exp (-t * (n : ℝ) / ((n : ℝ) - 1)) := by
    intro i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hi
    simp only [hi, ↓reduceIte, mul_div_assoc]
  rw [Finset.sum_congr rfl h_same]
  -- The sum of n-1 constant terms equals (n-1) * term
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Card of erased set = n - 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin n))]
  rw [Finset.card_univ, Fintype.card_fin]
  -- (n-1) · (n/(n-1)) = n
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h1 : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn'
    linarith
  -- Need to convert ↑(n - 1) to (n : ℝ) - 1
  have h_cast : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_of_lt hn')]
    simp
  rw [h_cast]
  field_simp [hn1]

/-- Explicit formula for the complete graph heat trace derivative:
    P'(t) = -exp(-tn/(n-1))

    The derivative is -(1/n) Σᵢ λᵢ exp(-t λᵢ).
    For K_n, the weighted sum equals n · exp(-tn/(n-1)).
    So P'(t) = -(1/n) · n · exp(...) = -exp(-tn/(n-1)). -/
theorem completeGraph_heatTraceDerivative_formula (hn' : 1 < n) (t : ℝ) :
    heatTraceDerivative n (completeGraphEigenvalues n) t =
    -Real.exp (-t * n / (n - 1 : ℝ)) := by
  unfold heatTraceDerivative
  rw [eigenvalue_weighted_sum_split n hn' t]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.lt_trans Nat.zero_lt_one hn'))
  field_simp [hn0]

/-- In the limit n → ∞, the complete graph heat trace derivative approaches -exp(-t).

    From the formula: P'(t) = -exp(-tn/(n-1))
    As n → ∞: n/(n-1) → 1, so P'(t) → -exp(-t). -/
theorem completeGraph_heatTraceDerivative_limit (t : ℝ) :
    Tendsto (fun m : ℕ =>
      if hm : 0 < m then
        have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        heatTraceDerivative m (completeGraphEigenvalues m) t
      else 0)
    atTop (𝓝 (-Real.exp (-t))) := by
  -- For m > 1, use the explicit formula and take limits
  have h_formula : (fun m : ℕ => -Real.exp (-t * (m : ℝ) / ((m : ℝ) - 1))) =ᶠ[atTop]
      (fun m => if hm : 0 < m then
        have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        heatTraceDerivative m (completeGraphEigenvalues m) t
      else 0) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm_pos : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
    simp only [dif_pos hm_pos]
    have _inst : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
    rw [completeGraph_heatTraceDerivative_formula m hm t]
  apply Tendsto.congr' h_formula
  -- Now prove the limit of the explicit expression: -exp(-t·m/(m-1)) → -exp(-t)
  -- exp(-t·m/(m-1)) → exp(-t) via ratio_limit and continuity
  have h_arg : Tendsto (fun m : ℕ => -t * (m : ℝ) / ((m : ℝ) - 1)) atTop (𝓝 (-t)) := by
    have h_ratio : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) - 1)) atTop (𝓝 1) := ratio_limit
    have h_mul : Tendsto (fun m : ℕ => -t * ((m : ℝ) / ((m : ℝ) - 1))) atTop (𝓝 (-t * 1)) :=
      Tendsto.const_mul (-t) h_ratio
    simp only [mul_one] at h_mul
    convert h_mul using 1
    ext m
    ring
  have h_exp : Tendsto (fun m : ℕ => Real.exp (-t * (m : ℝ) / ((m : ℝ) - 1))) atTop (𝓝 (Real.exp (-t))) :=
    (Real.continuous_exp.tendsto (-t)).comp h_arg
  -- -exp(...) → -exp(-t)
  exact Tendsto.neg h_exp

/-- **Main Theorem**: The spectral dimension of K_n evaluated at t=1 approaches 2 as n → ∞.

    Note on scale dependence: In the n → ∞ limit, D_S(t) = 2t for ALL t > 0.
    The value D_S = 2 is specific to the evaluation point t = 1, which corresponds
    to the natural eigenvalue scale t ~ 1/λ_min where λ_min = n/(n-1) → 1.

    Proof sketch:
    - For K_n: P(t) = (1/n)[1 + (n-1)exp(-tn/(n-1))]
    - As n → ∞: P(t) → exp(-t)
    - For P(t) = exp(-t): P'(t) = -exp(-t)
    - D_S(t) = -2t × P'(t)/P(t) = -2t × (-1) = 2t  (linear in t, not a plateau)
    - At t = 1: D_S(1) = 2

    This theorem proves only the t=1 case. The general D_S(t) = 2t behavior
    means there is no spectral dimension plateau for K_n; the physically relevant
    statement is that D_S at eigenvalue scale equals 2. -/
theorem completeGraph_spectralDimension_two :
    Filter.Tendsto (fun m : ℕ =>
      if hm : 0 < m then
        have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        runningSpectralDimension m (completeGraphEigenvalues m) 1
      else 0)
    Filter.atTop (nhds 2) := by
  -- Strategy: D_S(1) = -2 · 1 · P'(1)/P(1)
  -- As n → ∞: P'(1) → -exp(-1), P(1) → exp(-1)
  -- So P'(1)/P(1) → -1, and D_S(1) → -2 · 1 · (-1) = 2

  -- Step 1: Show the function equals an explicit formula eventually
  have h_formula : (fun m : ℕ =>
      2 * Real.exp (-(m : ℝ) / ((m : ℝ) - 1)) /
      ((1 / m : ℝ) + ((m - 1 : ℝ) / m) * Real.exp (-(m : ℝ) / ((m : ℝ) - 1)))) =ᶠ[atTop]
      (fun m => if hm : 0 < m then
        have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        runningSpectralDimension m (completeGraphEigenvalues m) 1
      else 0) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm_pos : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
    simp only [dif_pos hm_pos]
    have _inst : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
    -- Unfold definitions and use formulas
    unfold runningSpectralDimension heatTraceDerivative heatTrace
    simp only [completeGraphEigenvalues]
    -- Need to simplify the sums
    have hne1 : (m : ℝ) - 1 ≠ 0 := by
      have h1 : (1 : ℝ) < m := Nat.one_lt_cast.mpr hm
      linarith
    have hne0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm_pos)
    -- Use the eigenvalue_sum_split and eigenvalue_weighted_sum_split lemmas
    have h_sum := eigenvalue_sum_split m hm 1
    have h_wsum := eigenvalue_weighted_sum_split m hm 1
    simp only [completeGraphEigenvalues] at h_sum h_wsum
    rw [h_sum, h_wsum]
    -- The goal is now algebra: simplify the ratio
    -- LHS: 2 * exp(-m/(m-1)) / (1/m + (m-1)/m * exp(-m/(m-1)))
    -- RHS: -2 * 1 * (-(1/m) * (m * exp(-m/(m-1)))) / ((1/m) * (1 + (m-1)*exp(-m/(m-1))))
    -- These are equal after simplification
    field_simp [hne0, hne1]
  apply Tendsto.congr' h_formula

  -- Step 2: Prove the limit of the explicit formula
  -- As m → ∞: exp(-m/(m-1)) → exp(-1), 1/m → 0, (m-1)/m → 1
  -- So: 2*exp(-1) / (0 + 1*exp(-1)) = 2

  -- exp(-m/(m-1)) → exp(-1)
  have h_arg : Tendsto (fun m : ℕ => -(m : ℝ) / ((m : ℝ) - 1)) atTop (𝓝 (-1)) := by
    have h_ratio : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) - 1)) atTop (𝓝 1) := ratio_limit
    have h_neg : Tendsto (fun m : ℕ => -((m : ℝ) / ((m : ℝ) - 1))) atTop (𝓝 (-1)) :=
      Tendsto.neg h_ratio
    convert h_neg using 1
    ext m
    ring

  have h_exp : Tendsto (fun m : ℕ => Real.exp (-(m : ℝ) / ((m : ℝ) - 1))) atTop (𝓝 (Real.exp (-1))) :=
    (Real.continuous_exp.tendsto (-1)).comp h_arg

  -- 1/m → 0
  have h_inv : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (𝓝 0) := by
    have h := @tendsto_one_div_atTop_nhds_zero_nat ℝ _ _
    convert h using 1

  -- (m-1)/m → 1
  have h_coef : Tendsto (fun m : ℕ => ((m : ℝ) - 1) / (m : ℝ)) atTop (𝓝 1) := ratio_limit'

  -- ((m-1)/m) * exp(...) → 1 * exp(-1)
  have h_term : Tendsto (fun m : ℕ => ((m : ℝ) - 1) / (m : ℝ) * Real.exp (-(m : ℝ) / ((m : ℝ) - 1)))
      atTop (𝓝 (1 * Real.exp (-1))) := Tendsto.mul h_coef h_exp

  -- Denominator: 1/m + ((m-1)/m)*exp(...) → 0 + 1*exp(-1) = exp(-1)
  have h_denom : Tendsto (fun m : ℕ =>
      (1 / m : ℝ) + ((m - 1 : ℝ) / m) * Real.exp (-(m : ℝ) / ((m : ℝ) - 1)))
      atTop (𝓝 (0 + 1 * Real.exp (-1))) := Tendsto.add h_inv h_term
  simp only [zero_add, one_mul] at h_denom

  -- Numerator: 2 * exp(...) → 2 * exp(-1)
  have h_numer : Tendsto (fun m : ℕ => 2 * Real.exp (-(m : ℝ) / ((m : ℝ) - 1)))
      atTop (𝓝 (2 * Real.exp (-1))) := Tendsto.const_mul 2 h_exp

  -- exp(-1) ≠ 0
  have h_exp_ne : Real.exp (-1) ≠ 0 := Real.exp_ne_zero (-1)

  -- Ratio: 2*exp(-1) / exp(-1) = 2
  have h_ratio_lim : Tendsto (fun m : ℕ =>
      2 * Real.exp (-(m : ℝ) / ((m : ℝ) - 1)) /
      ((1 / m : ℝ) + ((m - 1 : ℝ) / m) * Real.exp (-(m : ℝ) / ((m : ℝ) - 1))))
      atTop (𝓝 (2 * Real.exp (-1) / Real.exp (-1))) := Tendsto.div h_numer h_denom h_exp_ne

  -- 2 * exp(-1) / exp(-1) = 2
  have h_val : 2 * Real.exp (-1) / Real.exp (-1) = 2 := by
    field_simp [h_exp_ne]

  rw [h_val] at h_ratio_lim
  exact h_ratio_lim

/-- Quantitative spectral dimension bound: for any ε > 0, there exists n₀
    such that for all n ≥ n₀ with n > 0, |D_S(K_n, 1) - 2| < ε.

    Extracts an explicit (non-constructive) threshold from the
    qualitative Tendsto proof of completeGraph_spectralDimension_two. -/
theorem spectralDimension_quantitative (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ m : ℕ, n₀ ≤ m → (hm_pos : 0 < m) →
    have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
    |runningSpectralDimension m (completeGraphEigenvalues m) 1 - 2| < ε := by
  -- Extract from completeGraph_spectralDimension_two
  have h_tend := completeGraph_spectralDimension_two
  -- Use Metric.ball_mem_nhds to get ball ε around 2 in nhds
  have h_ball : Metric.ball 2 ε ∈ nhds (2 : ℝ) := Metric.ball_mem_nhds 2 hε
  have h_ev := h_tend.eventually h_ball
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨N, hN⟩ := h_ev
  use max N 1
  intro m hm hm_pos _
  have hm_N : N ≤ m := le_trans (le_max_left N 1) hm
  have h_mem := hN m hm_N
  -- h_mem : dist (if 0 < m then D_S(K_m) else 0) 2 < ε
  simp only [dif_pos hm_pos] at h_mem
  -- Convert dist to |· - 2| via Real.dist_eq
  rwa [Real.dist_eq] at h_mem

/-!
## Crossing Width Bound

The crossing width measures how long (in log₁₀-space) the spectral dimension
stays near the value 2. For the limiting linear spectral dimension D_S(t) = 2t,
the crossing region {t > 0 : |D_S(t) - 2| < ε} = (1 - ε/2, 1 + ε/2),
and its width in log₁₀(t)-space is bounded.
-/

/-- The crossing width in log₁₀(t)-space for the linear spectral dimension D_S(t) = 2t.
    This is log₁₀((1 + ε/2) / (1 - ε/2)). -/
noncomputable def linearDS_crossingWidth (ε : ℝ) : ℝ :=
  Real.log ((1 + ε / 2) / (1 - ε / 2)) / Real.log 10

/-- The crossing width for D_S(t) = 2t is bounded by ε / ((1 - ε/2) · ln(10)).

    Proof: Using log(x) ≤ x - 1 for all x > 0, applied to x = (1+ε/2)/(1-ε/2):
    log((1+ε/2)/(1-ε/2)) ≤ (1+ε/2)/(1-ε/2) - 1 = ε/(1-ε/2).
    Dividing by log(10) gives the result. -/
theorem linearDS_crossingWidth_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 2) :
    linearDS_crossingWidth ε ≤ ε / ((1 - ε / 2) * Real.log 10) := by
  unfold linearDS_crossingWidth
  -- Key setup: let r = (1 + ε/2) / (1 - ε/2)
  have h_denom_pos : 0 < 1 - ε / 2 := by linarith
  have h_numer_pos : 0 < 1 + ε / 2 := by linarith
  have h_r_pos : 0 < (1 + ε / 2) / (1 - ε / 2) := div_pos h_numer_pos h_denom_pos
  have h_log10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num : (1:ℝ) < 10)
  -- Use log(x) ≤ x - 1 for x > 0
  have h_log_bound : Real.log ((1 + ε / 2) / (1 - ε / 2)) ≤
      (1 + ε / 2) / (1 - ε / 2) - 1 :=
    Real.log_le_sub_one_of_pos h_r_pos
  -- Simplify: (1 + ε/2)/(1 - ε/2) - 1 = ε/(1 - ε/2)
  have h_denom_ne : (1 : ℝ) - ε / 2 ≠ 0 := ne_of_gt h_denom_pos
  have h_simp : (1 + ε / 2) / (1 - ε / 2) - 1 = ε / (1 - ε / 2) := by
    rw [div_sub_one h_denom_ne]
    congr 1
    ring
  rw [h_simp] at h_log_bound
  -- Now: log(r) / log(10) ≤ (ε/(1-ε/2)) / log(10) = ε / ((1-ε/2) * log(10))
  rw [show ε / ((1 - ε / 2) * Real.log 10) = ε / (1 - ε / 2) / Real.log 10
    from (div_div ε (1 - ε / 2) (Real.log 10)).symm]
  exact div_le_div_of_nonneg_right h_log_bound (le_of_lt h_log10_pos)

end SpectralDimension
