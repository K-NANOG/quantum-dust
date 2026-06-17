/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenan Oggad

Exact finite-n polynomial moments of the squared overlap (Proposition II.1 / prop:cv2), 0 axioms.

HONEST SCOPE. For Haar-random pure states in dimension `n = m+1` the squared overlap
`u = |⟨ψ|φ⟩|²` has the Beta(1,n) law with density `n·(1-u)^{n-1} = (m+1)·(1-u)^m` on `[0,1]`.
Its exact finite-`n` polynomial moments are machine-checked here by explicit antiderivatives
(`E[u] = 1/(n+1)`, `E[u²] = 2/((n+1)(n+2))`). The half-integer moment `E[√u]` and the
`(4-π)/(π²n)` arcsin/Gamma-ratio asymptotic that feed `CV²` remain page proofs: Mathlib carries
only `Complex.betaIntegral`, so the half-integer Beta needs a Complex→Real bridge not formalized
here. The seam: polynomial moments verified, the `√u` moment and the asymptotic page-proved.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Verified.BetaMoments

open MeasureTheory

/-- Pointwise derivative of `x ↦ (1-x)^k`. -/
private lemma hasDerivAt_one_sub_pow (k : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => (1 - x) ^ k) ((k : ℝ) * (1 - u) ^ (k - 1) * (-1)) u :=
  ((hasDerivAt_id u).const_sub (1 : ℝ)).pow k

/-- **First raw integral (0 axioms).** `∫₀¹ u·(1-u)^m du = 1/((m+1)(m+2))`, by the explicit
antiderivative `F(u) = -(1-u)^{m+1}/(m+1) + (1-u)^{m+2}/(m+2)`. -/
theorem integral_u_mul_one_sub_pow (m : ℕ) :
    ∫ u in (0:ℝ)..1, u * (1 - u) ^ m = 1 / (((m:ℝ) + 1) * ((m:ℝ) + 2)) := by
  have hm1 : ((m:ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m:ℝ) + 2) ≠ 0 := by positivity
  have key : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => -((1 - x) ^ (m + 1) / ((m:ℝ) + 1))
          + (1 - x) ^ (m + 2) / ((m:ℝ) + 2)) (u * (1 - u) ^ m) u := by
    intro u _
    have h := HasDerivAt.add
      (HasDerivAt.neg (HasDerivAt.div_const (hasDerivAt_one_sub_pow (m + 1) u) ((m:ℝ) + 1)))
      (HasDerivAt.div_const (hasDerivAt_one_sub_pow (m + 2) u) ((m:ℝ) + 2))
    convert h using 1
    rw [show m + 1 - 1 = m from rfl, show m + 2 - 1 = m + 1 from rfl, pow_succ (1 - u) m]
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
        ((continuous_id.mul ((continuous_const.sub continuous_id).pow m)).intervalIntegrable 0 1)]
  norm_num
  field_simp
  ring

/-- **First moment (0 axioms).** For the Beta(1, m+1) density `(m+1)(1-u)^m`, `E[u] = 1/(m+2)`,
i.e. `1/(n+1)` with `n = m+1`. -/
theorem beta_first_moment (m : ℕ) :
    ∫ u in (0:ℝ)..1, ((m:ℝ) + 1) * (u * (1 - u) ^ m) = 1 / ((m:ℝ) + 2) := by
  have hm1 : ((m:ℝ) + 1) ≠ 0 := by positivity
  rw [intervalIntegral.integral_const_mul, integral_u_mul_one_sub_pow]
  field_simp

/-- **Second raw integral (0 axioms).** `∫₀¹ u²·(1-u)^m du = 2/((m+1)(m+2)(m+3))`, by the
explicit antiderivative `G(u) = -(1-u)^{m+1}/(m+1) + 2(1-u)^{m+2}/(m+2) - (1-u)^{m+3}/(m+3)`. -/
theorem integral_u_sq_mul_one_sub_pow (m : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ 2 * (1 - u) ^ m
      = 2 / (((m:ℝ) + 1) * ((m:ℝ) + 2) * ((m:ℝ) + 3)) := by
  have hm1 : ((m:ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m:ℝ) + 2) ≠ 0 := by positivity
  have hm3 : ((m:ℝ) + 3) ≠ 0 := by positivity
  have key : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => -((1 - x) ^ (m + 1) / ((m:ℝ) + 1))
          + 2 * ((1 - x) ^ (m + 2) / ((m:ℝ) + 2))
          + -((1 - x) ^ (m + 3) / ((m:ℝ) + 3))) (u ^ 2 * (1 - u) ^ m) u := by
    intro u _
    have h := HasDerivAt.add (HasDerivAt.add
      (HasDerivAt.neg (HasDerivAt.div_const (hasDerivAt_one_sub_pow (m + 1) u) ((m:ℝ) + 1)))
      (HasDerivAt.const_mul 2
        (HasDerivAt.div_const (hasDerivAt_one_sub_pow (m + 2) u) ((m:ℝ) + 2))))
      (HasDerivAt.neg (HasDerivAt.div_const (hasDerivAt_one_sub_pow (m + 3) u) ((m:ℝ) + 3)))
    convert h using 1
    rw [show m + 1 - 1 = m from rfl, show m + 2 - 1 = m + 1 from rfl,
        show m + 3 - 1 = m + 2 from rfl]
    simp only [pow_succ]
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
        (((continuous_id.pow 2).mul
          ((continuous_const.sub continuous_id).pow m)).intervalIntegrable 0 1)]
  norm_num
  field_simp
  ring

/-- **Second moment (0 axioms).** For the Beta(1, m+1) density `(m+1)(1-u)^m`,
`E[u²] = 2/((m+2)(m+3))`, i.e. `2/((n+1)(n+2))` with `n = m+1`. -/
theorem beta_second_moment (m : ℕ) :
    ∫ u in (0:ℝ)..1, ((m:ℝ) + 1) * (u ^ 2 * (1 - u) ^ m)
      = 2 / (((m:ℝ) + 2) * ((m:ℝ) + 3)) := by
  have hm1 : ((m:ℝ) + 1) ≠ 0 := by positivity
  rw [intervalIntegral.integral_const_mul, integral_u_sq_mul_one_sub_pow]
  field_simp

/-- **Tail / survival integral (0 axioms).** `∫ₓ¹ (m+1)(1-u)^m du = (1-x)^{m+1}`, the survival
function of the Beta(1, m+1) law: with `n = m+1`, this is `P(u > x) = (1-x)^n` for the squared
overlap `u ~ Beta(1,n)`. This is the per-pair tail that feeds the empirical-collapse union bound
(`Verified/EmpiricalCollapse.lean`). Antiderivative `-(1-u)^{m+1}`, via the same FTC machinery. -/
theorem beta_tail (m : ℕ) (x : ℝ) :
    ∫ u in x..1, ((m:ℝ) + 1) * (1 - u) ^ m = (1 - x) ^ (m + 1) := by
  have key : ∀ u ∈ Set.uIcc x 1,
      HasDerivAt (fun y : ℝ => -((1 - y) ^ (m + 1))) (((m:ℝ) + 1) * (1 - u) ^ m) u := by
    intro u _
    have h := (hasDerivAt_one_sub_pow (m + 1) u).neg
    convert h using 1
    rw [show m + 1 - 1 = m from rfl]
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
        ((continuous_const.mul ((continuous_const.sub continuous_id).pow m)).intervalIntegrable x 1)]
  simp

end Verified.BetaMoments
