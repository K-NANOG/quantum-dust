/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenan Oggad

Exact power-law plateau (Theorem IV.4, the regular-variation half — EXACT special case), 0 axioms.

HONEST SCOPE. The running-plateau half of the faithfulness-transfer theorem needs Karamata's
Tauberian theorem and the monotone-density theorem for the general slowly-varying density
`N(λ) = λ^{d/2} · ℓ(λ)`; Mathlib carries neither, so that generalization stays a page proof
(Bingham–Goldie–Teugels §1.7). The PURE power-law case `N(λ) = A·λ^{d/2}` needs neither and is
formalized here in full:
  * `heatTrace_powerLaw` — the heat trace `Θ(t) = ∫₀^∞ e^{-tλ} dN(λ)`, i.e.
    `∫₀^∞ A·(d/2)·λ^{d/2-1}·e^{-tλ} dλ`, is exactly `A·Γ(1+d/2)·t^{-d/2}` for every `t > 0`
    (Mathlib's scaled Gamma integral `integral_rpow_mul_exp_neg_mul_Ioi`).
  * `running_dimension_of_closedForm` / `powerLaw_spectralDimension` — for that closed form the
    running spectral dimension `D_S(t) = -2t·Θ'(t)/Θ(t)` equals `d` EXACTLY, for every `t > 0`,
    with no limit and no Tauberian input.
Bridge: by `heatTrace_powerLaw` the heat trace IS the closed form `powerLaw_spectralDimension`
differentiates, so the running dimension of the power-law heat trace is `d`. The seam — exact
power law verified, slowly-varying generalization page-proved — is exactly Theorem IV.4's split.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Verified.PowerLaw

open MeasureTheory Real Set

/-- **Power-law heat trace (0 axioms).** For an integrated density `N(λ) = A·λ^{d/2}` the
Stieltjes heat trace `Θ(t) = ∫₀^∞ e^{-tλ} dN(λ) = ∫₀^∞ A·(d/2)·λ^{d/2-1}·e^{-tλ} dλ` evaluates
to the closed form `A·Γ(1+d/2)·t^{-d/2}` for every `t > 0`. -/
theorem heatTrace_powerLaw (A d t : ℝ) (hd : 0 < d) (ht : 0 < t) :
    ∫ lam in Ioi (0 : ℝ), A * (d / 2) * (lam ^ (d / 2 - 1) * Real.exp (-(t * lam)))
      = A * Real.Gamma (1 + d / 2) * t ^ (-(d / 2)) := by
  have hd2 : (0 : ℝ) < d / 2 := by linarith
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi hd2 ht, one_div,
      Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, add_comm (1 : ℝ) (d / 2),
      Real.Gamma_add_one (ne_of_gt hd2)]
  ring

/-- **Exact running dimension of a power-law heat trace (0 axioms).** For the closed form
`Θ(t) = C·t^{-d/2}` with `C ≠ 0`, the running spectral dimension `D_S(t) = -2t·Θ'(t)/Θ(t)`
equals `d` exactly for every `t > 0` — no limit, no Tauberian input. -/
theorem running_dimension_of_closedForm (C d t : ℝ) (hC : C ≠ 0) (ht : 0 < t) :
    -2 * t * deriv (fun s : ℝ => C * s ^ (-(d / 2))) t / (C * t ^ (-(d / 2))) = d := by
  have hderiv : HasDerivAt (fun s : ℝ => C * s ^ (-(d / 2)))
      (C * (-(d / 2) * t ^ (-(d / 2) - 1))) t :=
    (Real.hasDerivAt_rpow_const (p := -(d / 2)) (Or.inl (ne_of_gt ht))).const_mul C
  rw [hderiv.deriv]
  have hXne : t ^ (-(d / 2)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hX : t ^ (-(d / 2) - 1) = t ^ (-(d / 2)) / t := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  rw [hX]
  field_simp

/-- **Power-law plateau, end to end (0 axioms).** The heat trace of `N(λ)=A·λ^{d/2}` has closed
form `A·Γ(1+d/2)·t^{-d/2}` (`heatTrace_powerLaw`), and that closed form has running spectral
dimension exactly `d` for every `t > 0`. -/
theorem powerLaw_spectralDimension (A d t : ℝ) (hA : A ≠ 0) (hd : 0 < d) (ht : 0 < t) :
    -2 * t * deriv (fun s : ℝ => A * Real.Gamma (1 + d / 2) * s ^ (-(d / 2))) t
      / (A * Real.Gamma (1 + d / 2) * t ^ (-(d / 2))) = d := by
  have hG : 0 < Real.Gamma (1 + d / 2) := Real.Gamma_pos_of_pos (by linarith)
  exact running_dimension_of_closedForm (A * Real.Gamma (1 + d / 2)) d t
    (mul_ne_zero hA (ne_of_gt hG)) ht

end Verified.PowerLaw
