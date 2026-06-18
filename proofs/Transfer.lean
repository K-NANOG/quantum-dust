/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenan Oggad

Faithfulness transfers the EXPONENT (Theorem IV.4, the unconditional half) — 0 axioms.

HONEST SCOPE. This formalizes the sandwich-free half of the faithfulness-transfer theorem:
the eigenvalue sandwich `SpectrallyFaithful` forces a two-sided squeeze on the heat trace,
`ΘG (C·t) ≤ ΘM t ≤ ΘG (c·t)`, and that squeeze transfers the scaling exponent
`log Θ(t) / log t`. The RUNNING-PLATEAU half (`D_S(t) → d` under regular variation of the
density, by Karamata's Tauberian theorem and the monotone-density theorem) is proved on the
page and is NOT formalized here: Mathlib carries no Karamata / regular-variation theory, and
importing it as an axiom would defeat the 0-axiom guarantee. The seam — exponent free from the
sandwich, plateau only under regular variation — is exactly the content of the page proof.

The heat-trace squeeze is over a finite spectrum (the link graph). The exponent statement is
abstract over `ℝ → ℝ` heat traces, since a genuine negative exponent `L = -d/2` needs
eigenvalues accumulating at zero, the continuum / `N → ∞` object that no finite graph carries.
-/
import proofs.CompleteGraph
import proofs.Separation

namespace Verified.Transfer

open SpectralDimension Verified.Separation
open Filter Topology Real

/-- **Heat-trace squeeze from faithfulness (0 axioms).** If `eigM` is spectrally faithful to
a spectrum `eigG`, the heat traces squeeze with the sandwich constants `c, C`:
`ΘG (C·t) ≤ ΘM t ≤ ΘG (c·t)` for every `t ≥ 0`. This is the unconditional core of
Theorem IV.4; it owes nothing to regular variation. -/
theorem heatTrace_faithful_squeeze {N : ℕ} (eigG eigM : Fin N → ℝ)
    (hf : SpectrallyFaithful eigG eigM) {t : ℝ} (ht : 0 ≤ t) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      heatTrace N eigG (C * t) ≤ heatTrace N eigM t ∧
      heatTrace N eigM t ≤ heatTrace N eigG (c * t) := by
  obtain ⟨c, C, hc, hC, hsand⟩ := hf
  refine ⟨c, C, hc, hC, ?_, ?_⟩
  · simp only [heatTrace]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hsand i).2 ht])
  · simp only [heatTrace]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hsand i).1 ht])

/-- Dilating the argument by a positive constant does not change the log-scaling:
`log (a·t) / log t → 1` as `t → ∞`. -/
private lemma dilation_log_ratio (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => Real.log (a * t) / Real.log t) atTop (𝓝 1) := by
  have h0 : Tendsto (fun t => Real.log a / Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h1 : Tendsto (fun t => Real.log a / Real.log t + 1) atTop (𝓝 1) := by
    simpa using h0.add_const (1 : ℝ)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt ht0), add_div, div_self hlogt]

/-- **Exponent transfer (0 axioms).** If two heat-trace functions satisfy the faithfulness
squeeze `ΘG (C·t) ≤ ΘM t ≤ ΘG (c·t)` eventually (with `0 < c`, `0 < C`, and `ΘG (C·t) > 0`),
and `ΘG` has scaling exponent `L` in the sense `log (ΘG t) / log t → L`, then `ΘM` carries the
SAME exponent. This is the exponent crossing the sandwich, unconditionally; the running plateau
does not cross it (page proof, needs regular variation). -/
theorem exponent_transfer (ΘG ΘM : ℝ → ℝ) (c C L : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hposCt : ∀ᶠ t in atTop, 0 < ΘG (C * t))
    (hlo : ∀ᶠ t in atTop, ΘG (C * t) ≤ ΘM t)
    (hhi : ∀ᶠ t in atTop, ΘM t ≤ ΘG (c * t))
    (hexp : Tendsto (fun t => Real.log (ΘG t) / Real.log t) atTop (𝓝 L)) :
    Tendsto (fun t => Real.log (ΘM t) / Real.log t) atTop (𝓝 L) := by
  have hCt : Tendsto (fun t : ℝ => C * t) atTop atTop := Tendsto.const_mul_atTop hC tendsto_id
  have hct : Tendsto (fun t : ℝ => c * t) atTop atTop := Tendsto.const_mul_atTop hc tendsto_id
  have hAC : Tendsto (fun t => Real.log (ΘG (C * t)) / Real.log (C * t)) atTop (𝓝 L) := by
    have := hexp.comp hCt; simpa [Function.comp] using this
  have hAc : Tendsto (fun t => Real.log (ΘG (c * t)) / Real.log (c * t)) atTop (𝓝 L) := by
    have := hexp.comp hct; simpa [Function.comp] using this
  have hlow : Tendsto (fun t => Real.log (ΘG (C * t)) / Real.log t) atTop (𝓝 L) := by
    have hmul := hAC.mul (dilation_log_ratio C hC)
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (max 1 (1 / C))] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt (le_max_left _ _) ht
    have hCt1 : 1 < C * t := by
      have h := lt_of_le_of_lt (le_max_right _ _) ht
      have h2 := mul_lt_mul_of_pos_left h hC
      rwa [mul_one_div, div_self (ne_of_gt hC)] at h2
    have hlogCt : Real.log (C * t) ≠ 0 := ne_of_gt (Real.log_pos hCt1)
    have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    field_simp
  have hupp : Tendsto (fun t => Real.log (ΘG (c * t)) / Real.log t) atTop (𝓝 L) := by
    have hmul := hAc.mul (dilation_log_ratio c hc)
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (max 1 (1 / c))] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt (le_max_left _ _) ht
    have hct1 : 1 < c * t := by
      have h := lt_of_le_of_lt (le_max_right _ _) ht
      have h2 := mul_lt_mul_of_pos_left h hc
      rwa [mul_one_div, div_self (ne_of_gt hc)] at h2
    have hlogct : Real.log (c * t) ≠ 0 := ne_of_gt (Real.log_pos hct1)
    have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hposCt, hlo] with t ht hp hle
    have hlogt : 0 < Real.log t := Real.log_pos ht
    gcongr
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hposCt, hlo, hhi] with t ht hp hle hle2
    have hlogt : 0 < Real.log t := Real.log_pos ht
    have hMpos : 0 < ΘM t := lt_of_lt_of_le hp hle
    gcongr

end Verified.Transfer
