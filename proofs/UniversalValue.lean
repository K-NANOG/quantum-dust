/-
The Universal Kinematic Value (composed) — machine-checked, 0 axioms.

If a sequence of finite samples has (normalized-Laplacian) eigenvalues that become uniformly
ε_m-close to the complete-graph / equidistant eigenvalues with ε_m → 0, then the diffusion
probe reads spectral dimension D_S(1) → 2. This composes the perturbation→stability bounds
(Verified.Stability, the machine-checked form of "concentration ⇒ K_m") with the K_m limit
D_S(K_m,1)→2 (Verified.CompleteGraph). 0 physics axioms.

The upstream Lévy step ("concentration of measure ⇒ eigenvalues → K_m") is the cited input
(Ledoux 2001; Milman–Schechtman 1986), supplied here as the explicit hypothesis `h_close`.
-/
import Verified.Stability

namespace Verified.UniversalValue
open SpectralDimension Stability Filter Topology

theorem universal_value
    (eigM : (m : ℕ) → Fin m → ℝ) (epsSeq : ℕ → ℝ)
    (h_eps_pos : ∀ m, 0 ≤ epsSeq m)
    (h_eps_vanish : Tendsto epsSeq atTop (𝓝 0))
    (h_nonneg : ∀ m, ∀ i : Fin m, 0 ≤ eigM m i)
    (h_close : ∀ m, ∀ (hm : 0 < m), ∀ i : Fin m,
      haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
      |eigM m i - completeGraphEigenvalues m i| ≤ epsSeq m) :
    Tendsto (fun m : ℕ =>
      if hm : 0 < m then
        haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        runningSpectralDimension m (eigM m) 1
      else 0)
    atTop (𝓝 2) := by
  -- K_m heat-trace limit at t = 1 (from L3 support), in heatTrace form.
  have hPk : Tendsto (fun m : ℕ => if hm : 0 < m then
      haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
      heatTrace m (completeGraphEigenvalues m) 1 else 0) atTop (𝓝 (Real.exp (-1))) := by
    refine (completeGraph_heatTrace_limit 1 (by norm_num)).congr fun m => ?_
    by_cases hm : 0 < m
    · simp only [dif_pos hm]; rfl
    · simp only [dif_neg hm]
  -- K_m heat-trace-derivative limit at t = 1.
  have hDk : Tendsto (fun m : ℕ => if hm : 0 < m then
      haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
      heatTraceDerivative m (completeGraphEigenvalues m) 1 else 0) atTop (𝓝 (-Real.exp (-1))) := by
    refine (completeGraph_heatTraceDerivative_limit 1).congr fun m => ?_
    by_cases hm : 0 < m
    · simp only [dif_pos hm]
    · simp only [dif_neg hm]
  -- Perturbed heat trace → exp(-1) (perturbation diff → 0 via Chebyshev/L2 bound).
  have hPe : Tendsto (fun m : ℕ => if hm : 0 < m then
      haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
      heatTrace m (eigM m) 1 else 0) atTop (𝓝 (Real.exp (-1))) := by
    have hd0 : Tendsto (fun m : ℕ =>
        (if hm : 0 < m then haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
          heatTrace m (eigM m) 1 else 0)
        - (if hm : 0 < m then haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
          heatTrace m (completeGraphEigenvalues m) 1 else 0)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h_eps_vanish
      filter_upwards [eventually_gt_atTop 0] with m hm
      haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
      simp only [dif_pos hm, Real.norm_eq_abs]
      simpa using heatTrace_perturbation_bound m (eigM m) 1 (epsSeq m) (by norm_num)
        (h_eps_pos m) (h_nonneg m) (h_close m hm)
    have h := hPk.add hd0
    rw [add_zero] at h
    exact h.congr fun m => by ring
  -- Perturbed heat-trace derivative → -exp(-1) (diff → 0; M = 2 + ε_m bound).
  have hDe : Tendsto (fun m : ℕ => if hm : 0 < m then
      haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
      heatTraceDerivative m (eigM m) 1 else 0) atTop (𝓝 (-Real.exp (-1))) := by
    have hg : Tendsto (fun m => ((2 + epsSeq m) * 1 + 1) * epsSeq m) atTop (𝓝 0) := by
      have : Tendsto (fun m => ((2 + epsSeq m) * 1 + 1) * epsSeq m) atTop
          (𝓝 (((2 + 0) * 1 + 1) * 0)) :=
        ((((tendsto_const_nhds).add h_eps_vanish).mul tendsto_const_nhds).add
          tendsto_const_nhds).mul h_eps_vanish
      simpa using this
    have hd0 : Tendsto (fun m : ℕ =>
        (if hm : 0 < m then haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
          heatTraceDerivative m (eigM m) 1 else 0)
        - (if hm : 0 < m then haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
          heatTraceDerivative m (completeGraphEigenvalues m) 1 else 0)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [eventually_gt_atTop 1] with m hm
      have hm0 : 0 < m := by omega
      haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm0⟩
      simp only [dif_pos hm0, Real.norm_eq_abs]
      have hMbound : ∀ i, eigM m i ≤ 2 + epsSeq m := by
        intro i
        have hcg2 : completeGraphEigenvalues m i ≤ 2 := by
          simp only [completeGraphEigenvalues]
          split
          · norm_num
          · have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ m by omega)
            rw [div_le_iff₀ (by linarith)]; linarith
        have hcl := (abs_le.mp (h_close m hm0 i)).2
        linarith
      exact heatTraceDerivative_perturbation_bound m (eigM m) 1 (epsSeq m) (2 + epsSeq m)
        (by norm_num) (h_eps_pos m) (h_nonneg m) (h_close m hm0) hMbound
        (by linarith [h_eps_pos m])
    have h := hDk.add hd0
    rw [add_zero] at h
    exact h.congr fun m => by ring
  -- Assemble: D_S(eigM m, 1) = -2·1·P'/P → -2·(-exp(-1))/exp(-1) = 2.
  have hexp_ne : Real.exp (-1) ≠ 0 := Real.exp_ne_zero _
  have hfinal := (hDe.div hPe hexp_ne).const_mul (-2)
  have hval : (-2 : ℝ) * (-Real.exp (-1) / Real.exp (-1)) = 2 := by
    have h1 : Real.exp (-1) / Real.exp (-1) = 1 := div_self hexp_ne
    rw [neg_div, h1]; ring
  rw [hval] at hfinal
  refine hfinal.congr fun m => ?_
  by_cases hm : 0 < m
  · haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
    simp only [Pi.div_apply, dif_pos hm, runningSpectralDimension, mul_one, mul_div_assoc]
  · simp only [Pi.div_apply, dif_neg hm, zero_div, mul_zero]

end Verified.UniversalValue
