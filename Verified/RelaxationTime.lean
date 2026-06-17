/-
Convention-free relaxation-time crossing — machine-checked, 0 axioms.

For the single-cluster ("dust") spectrum {0, a^(m-1)} with a > 0, the running
spectral dimension evaluated at one relaxation time t = 1/a is EXACTLY
  D_S = 2(m-1)e^{-1} / (1 + (m-1)e^{-1}),
in which the eigenvalue `a` has cancelled. The crossing value is therefore
independent of the Laplacian normalization (normalized K_m has the nonzero
eigenvalue m/(m-1), the combinatorial one has m; both read this same value at
their own relaxation time 1/a), and it tends to 2 as m -> infinity.

This is the VALUE half of "the dust returns the diffusion's own dimension at the
single scale it possesses." The SLOPE statement (dD_S/dln t at the crossing is
nonzero, equal to the value in the linear regime) is proved on paper only — it
is a derivative of a log of a heat trace, not formalized here. 0 physics axioms.
-/
import Verified.CompleteGraph

namespace Verified.RelaxationTime

open SpectralDimension Filter Topology Real
open scoped BigOperators

/-- Single-cluster ("dust") spectrum: 0 on the constants, common value `a` elsewhere. -/
noncomputable def clusterEigenvalues (a : ℝ) (m : ℕ) [NeZero m] : Fin m → ℝ :=
  fun i => if i = 0 then 0 else a

/-- Heat-trace exponential sum for the single cluster: 1 + (m-1) e^{-ta}. -/
lemma cluster_sum_split (a : ℝ) (m : ℕ) [NeZero m] (hm : 1 < m) (t : ℝ) :
    ∑ i : Fin m, Real.exp (-t * clusterEigenvalues a m i) =
    1 + (m - 1 : ℝ) * Real.exp (-t * a) := by
  simp only [clusterEigenvalues]
  rw [← Finset.insert_erase (Finset.mem_univ (0 : Fin m)),
    Finset.sum_insert (by simp [Finset.mem_erase])]
  simp only [↓reduceIte, mul_zero, Real.exp_zero]
  congr 1
  have h_same : ∀ i ∈ Finset.univ.erase (0 : Fin m),
      Real.exp (-t * if i = 0 then 0 else a) = Real.exp (-t * a) := by
    intro i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hi
    simp only [hi, ↓reduceIte]
  rw [Finset.sum_congr rfl h_same, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin m)), Finset.card_univ,
    Fintype.card_fin]
  simp only [Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one]

/-- Weighted heat-trace sum for the single cluster: (m-1) a e^{-ta}. -/
lemma cluster_weighted_sum_split (a : ℝ) (m : ℕ) [NeZero m] (hm : 1 < m) (t : ℝ) :
    ∑ i : Fin m, clusterEigenvalues a m i * Real.exp (-t * clusterEigenvalues a m i) =
    (m - 1 : ℝ) * a * Real.exp (-t * a) := by
  simp only [clusterEigenvalues]
  rw [← Finset.insert_erase (Finset.mem_univ (0 : Fin m)),
    Finset.sum_insert (by simp [Finset.mem_erase])]
  simp only [↓reduceIte, mul_zero, Real.exp_zero, zero_mul, zero_add]
  have h_same : ∀ i ∈ Finset.univ.erase (0 : Fin m),
      (if i = 0 then 0 else a) * Real.exp (-t * if i = 0 then 0 else a)
        = a * Real.exp (-t * a) := by
    intro i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hi
    simp only [hi, ↓reduceIte]
  rw [Finset.sum_congr rfl h_same, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin m)), Finset.card_univ,
    Fintype.card_fin, Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one]
  ring

/-- **Convention-free crossing value (the eigenvalue cancels).** For `m > 1` and any
`a > 0`, the running spectral dimension of the single-cluster spectrum at one relaxation
time `t = 1/a` is `2(m-1)e^{-1}/(1+(m-1)e^{-1})` — independent of `a`. -/
theorem cluster_relaxation_formula (a : ℝ) (ha : 0 < a) (m : ℕ) [NeZero m] (hm : 1 < m) :
    runningSpectralDimension m (clusterEigenvalues a m) (1 / a) =
    2 * ((m : ℝ) - 1) * Real.exp (-1) / (1 + ((m : ℝ) - 1) * Real.exp (-1)) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hEpos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hm1 : (1 : ℝ) ≤ ((m : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hden : (1 : ℝ) + ((m : ℝ) - 1) * Real.exp (-1) ≠ 0 := by positivity
  unfold runningSpectralDimension heatTraceDerivative heatTrace
  rw [cluster_sum_split a m hm, cluster_weighted_sum_split a m hm]
  have hexp : Real.exp (-(1 / a) * a) = Real.exp (-1) := by
    congr 1; field_simp
  rw [hexp]
  field_simp

/-- **The dust returns two at its one relaxation time (machine-checked value).**
For every `a > 0`, `D_S` of the single-cluster spectrum at `t = 1/a` tends to `2`
as `m -> infinity`. Convention-free: the eigenvalue `a` cancelled in the formula
above, so the limit is the same for any normalization. -/
theorem cluster_spectralDimension_relaxation_two (a : ℝ) (ha : 0 < a) :
    Tendsto (fun m : ℕ =>
      if hm : 0 < m then
        haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        runningSpectralDimension m (clusterEigenvalues a m) (1 / a)
      else 0)
    atTop (nhds 2) := by
  have hEpos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  -- The explicit a-free formula, eventually.
  have h_formula : (fun m : ℕ =>
      2 * ((m : ℝ) - 1) * Real.exp (-1) / (1 + ((m : ℝ) - 1) * Real.exp (-1))) =ᶠ[atTop]
      (fun m => if hm : 0 < m then
        haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        runningSpectralDimension m (clusterEigenvalues a m) (1 / a) else 0) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm_pos : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
    simp only [dif_pos hm_pos]
    haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
    exact (cluster_relaxation_formula a ha m hm).symm
  refine Tendsto.congr' h_formula ?_
  -- 2(m-1)E/(1+(m-1)E) = 2 - 2/(1+(m-1)E) -> 2 - 0 = 2
  have hdiff : (fun m : ℕ =>
      2 - 2 / (1 + ((m : ℝ) - 1) * Real.exp (-1))) =ᶠ[atTop]
      (fun m : ℕ => 2 * ((m : ℝ) - 1) * Real.exp (-1) / (1 + ((m : ℝ) - 1) * Real.exp (-1))) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm1 : (1 : ℝ) ≤ ((m : ℝ) - 1) := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hden : (1 : ℝ) + ((m : ℝ) - 1) * Real.exp (-1) ≠ 0 := by positivity
    field_simp
    ring
  refine Tendsto.congr' hdiff ?_
  have htail : Tendsto (fun m : ℕ => 2 / (1 + ((m : ℝ) - 1) * Real.exp (-1)))
      atTop (nhds 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply Filter.tendsto_atTop_add_const_left
    apply Filter.Tendsto.atTop_mul_const hEpos
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have := h2.sub htail
  simpa using this

/-- **Fixed-clock closed form.** For `m > 1`, the running spectral dimension of the
single-cluster spectrum at the fixed probe time `t = 1` is `2a(m-1)e^{-a}/(1+(m-1)e^{-a})`. -/
theorem cluster_fixedclock_formula (a : ℝ) (m : ℕ) [NeZero m] (hm : 1 < m) :
    runningSpectralDimension m (clusterEigenvalues a m) 1 =
    2 * a * ((m : ℝ) - 1) * Real.exp (-a) / (1 + ((m : ℝ) - 1) * Real.exp (-a)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hEpos : (0 : ℝ) < Real.exp (-a) := Real.exp_pos _
  have hm1 : (1 : ℝ) ≤ ((m : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hden : (1 : ℝ) + ((m : ℝ) - 1) * Real.exp (-a) ≠ 0 := by positivity
  unfold runningSpectralDimension heatTraceDerivative heatTrace
  rw [cluster_sum_split a m hm 1, cluster_weighted_sum_split a m hm 1]
  simp only [neg_one_mul]
  field_simp

/-- **The full separation-gap limit, machine-checked.** For every `a`, the running
spectral dimension of the single-cluster spectrum at the fixed clock `t = 1` tends to
`2a` as `m -> infinity`. This is the limit half of the gap theorem (the stability half
is `Stability.spectralDimension_stability`); the complete graph is the case `a -> 1`. -/
theorem cluster_spectralDimension_fixed_two_a (a : ℝ) :
    Tendsto (fun m : ℕ =>
      if hm : 0 < m then
        haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        runningSpectralDimension m (clusterEigenvalues a m) 1
      else 0)
    atTop (nhds (2 * a)) := by
  have hEpos : (0 : ℝ) < Real.exp (-a) := Real.exp_pos _
  have h_formula : (fun m : ℕ =>
      2 * a * ((m : ℝ) - 1) * Real.exp (-a) / (1 + ((m : ℝ) - 1) * Real.exp (-a))) =ᶠ[atTop]
      (fun m => if hm : 0 < m then
        haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
        runningSpectralDimension m (clusterEigenvalues a m) 1 else 0) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm_pos : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
    simp only [dif_pos hm_pos]
    haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
    exact (cluster_fixedclock_formula a m hm).symm
  refine Tendsto.congr' h_formula ?_
  have hdiff : (fun m : ℕ =>
      2 * a - (2 * a) / (1 + ((m : ℝ) - 1) * Real.exp (-a))) =ᶠ[atTop]
      (fun m : ℕ => 2 * a * ((m : ℝ) - 1) * Real.exp (-a) / (1 + ((m : ℝ) - 1) * Real.exp (-a))) := by
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hm1 : (1 : ℝ) ≤ ((m : ℝ) - 1) := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hden : (1 : ℝ) + ((m : ℝ) - 1) * Real.exp (-a) ≠ 0 := by positivity
    field_simp
    ring
  refine Tendsto.congr' hdiff ?_
  have htail : Tendsto (fun m : ℕ => (2 * a) / (1 + ((m : ℝ) - 1) * Real.exp (-a)))
      atTop (nhds 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply Filter.tendsto_atTop_add_const_left
    apply Filter.Tendsto.atTop_mul_const hEpos
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2a : Tendsto (fun _ : ℕ => (2 * a : ℝ)) atTop (nhds (2 * a)) := tendsto_const_nhds
  have := h2a.sub htail
  simpa using this

/-! ## Class B: the two-scale ("band") spectrum — the eigenvalue does NOT cancel

The single cluster has one nonzero scale `a`; at its relaxation time `t = 1/a` the
eigenvalue cancels (`cluster_relaxation_formula`) and the crossing value is
convention-free, tending to 2.  A gapped spectrum with TWO nonzero scales `a ≠ b`
— the causal-set "band" (Class B), empirically `a ≈ 0.78`, `b ≈ 1.30`, ratio
`b/a ≈ 1.7` — is different: at the relaxation time `1/a` of the first scale the
second enters through the ratio `ρ = b/a`, which does NOT cancel.  In the
macroscopic-band limit (`p = q = r → ∞`) the value is
`L(ρ) = 2(e⁻¹ + ρe^{-ρ})/(e⁻¹ + e^{-ρ})`, with
`L(ρ) - 2 = 2e^{-ρ}(ρ-1)/(e⁻¹+e^{-ρ})`, so `L(ρ) = 2` iff `ρ = 1`.  Two distinct
scales (`ρ ≠ 1`) pin the relaxation reading off 2 by a definite amount set by the
spectral ratio — the formal root of Class B lying off the universal `2τ` line.
0 physics axioms. -/

/-- Two-scale ("band") spectrum on `Fin (p+q+1)`: `0` on the constants, `a` on a
block of size `p`, `b` on a block of size `q`. -/
noncomputable def twoClusterEigenvalues (a b : ℝ) (p q : ℕ) : Fin (p + q + 1) → ℝ :=
  fun i => if (i : ℕ) = 0 then 0 else if (i : ℕ) ≤ p then a else b

private lemma sum_pq_three_block {α : Type*} [AddCommMonoid α] (p q : ℕ) (g : ℕ → α) :
    ∑ j ∈ Finset.range (p + q + 1), g j
      = g 0 + (∑ j ∈ Finset.Ico 1 (p + 1), g j)
            + ∑ j ∈ Finset.Ico (p + 1) (p + q + 1), g j := by
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive g (by omega : (0:ℕ) ≤ 1) (by omega : (1:ℕ) ≤ p + q + 1),
    ← Finset.sum_Ico_consecutive g (by omega : (1:ℕ) ≤ p + 1) (by omega : (p + 1 : ℕ) ≤ p + q + 1)]
  have h0 : ∑ j ∈ Finset.Ico 0 1, g j = g 0 := by rw [Finset.sum_Ico_eq_sum_range]; simp
  rw [h0]; abel

/-- Heat-trace exponential sum for the two-scale band: `1 + p e^{-ta} + q e^{-tb}`. -/
lemma twoCluster_sum_split (a b : ℝ) (p q : ℕ) (t : ℝ) :
    ∑ i : Fin (p + q + 1), Real.exp (-t * twoClusterEigenvalues a b p q i)
      = 1 + (p : ℝ) * Real.exp (-t * a) + (q : ℝ) * Real.exp (-t * b) := by
  have hrw : ∀ i : Fin (p + q + 1), Real.exp (-t * twoClusterEigenvalues a b p q i)
      = Real.exp (-t * (if (i : ℕ) = 0 then (0:ℝ) else if (i : ℕ) ≤ p then a else b)) :=
    fun _ => rfl
  simp_rw [hrw]
  rw [Fin.sum_univ_eq_sum_range
        (fun j => Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b))) (p + q + 1),
      sum_pq_three_block p q]
  have hA : ∑ j ∈ Finset.Ico 1 (p + 1),
        Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b))
        = (p : ℝ) * Real.exp (-t * a) := by
    have hc : ∀ j ∈ Finset.Ico 1 (p + 1),
        Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b)) = Real.exp (-t * a) := by
      intro j hj; simp only [Finset.mem_Ico] at hj
      have hj0 : j ≠ 0 := by omega
      have hjp : j ≤ p := by omega
      simp [hj0, hjp]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; simp
  have hB : ∑ j ∈ Finset.Ico (p + 1) (p + q + 1),
        Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b))
        = (q : ℝ) * Real.exp (-t * b) := by
    have hc : ∀ j ∈ Finset.Ico (p + 1) (p + q + 1),
        Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b)) = Real.exp (-t * b) := by
      intro j hj; simp only [Finset.mem_Ico] at hj
      have hj0 : j ≠ 0 := by omega
      have hjp : ¬ j ≤ p := by omega
      simp [hj0, hjp]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hpq : p + q + 1 - (p + 1) = q := by omega
    rw [hpq]
  have h0 : Real.exp (-t * (if (0:ℕ) = 0 then (0:ℝ) else if (0:ℕ) ≤ p then a else b)) = 1 := by simp
  rw [h0, hA, hB]

/-- Weighted heat-trace sum for the two-scale band: `p a e^{-ta} + q b e^{-tb}`. -/
lemma twoCluster_weighted_sum_split (a b : ℝ) (p q : ℕ) (t : ℝ) :
    ∑ i : Fin (p + q + 1),
        twoClusterEigenvalues a b p q i * Real.exp (-t * twoClusterEigenvalues a b p q i)
      = (p : ℝ) * a * Real.exp (-t * a) + (q : ℝ) * b * Real.exp (-t * b) := by
  have hrw : ∀ i : Fin (p + q + 1),
      twoClusterEigenvalues a b p q i * Real.exp (-t * twoClusterEigenvalues a b p q i)
      = (if (i : ℕ) = 0 then (0:ℝ) else if (i : ℕ) ≤ p then a else b)
          * Real.exp (-t * (if (i : ℕ) = 0 then (0:ℝ) else if (i : ℕ) ≤ p then a else b)) :=
    fun _ => rfl
  simp_rw [hrw]
  rw [Fin.sum_univ_eq_sum_range
        (fun j => (if j = 0 then (0:ℝ) else if j ≤ p then a else b)
            * Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b))) (p + q + 1),
      sum_pq_three_block p q]
  have hA : ∑ j ∈ Finset.Ico 1 (p + 1),
        (if j = 0 then (0:ℝ) else if j ≤ p then a else b)
          * Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b))
        = (p : ℝ) * a * Real.exp (-t * a) := by
    have hc : ∀ j ∈ Finset.Ico 1 (p + 1),
        (if j = 0 then (0:ℝ) else if j ≤ p then a else b)
          * Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b)) = a * Real.exp (-t * a) := by
      intro j hj; simp only [Finset.mem_Ico] at hj
      have hj0 : j ≠ 0 := by omega
      have hjp : j ≤ p := by omega
      simp [hj0, hjp]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hp : p + 1 - 1 = p := by omega
    rw [hp]; ring
  have hB : ∑ j ∈ Finset.Ico (p + 1) (p + q + 1),
        (if j = 0 then (0:ℝ) else if j ≤ p then a else b)
          * Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b))
        = (q : ℝ) * b * Real.exp (-t * b) := by
    have hc : ∀ j ∈ Finset.Ico (p + 1) (p + q + 1),
        (if j = 0 then (0:ℝ) else if j ≤ p then a else b)
          * Real.exp (-t * (if j = 0 then (0:ℝ) else if j ≤ p then a else b)) = b * Real.exp (-t * b) := by
      intro j hj; simp only [Finset.mem_Ico] at hj
      have hj0 : j ≠ 0 := by omega
      have hjp : ¬ j ≤ p := by omega
      simp [hj0, hjp]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hpq : p + q + 1 - (p + 1) = q := by omega
    rw [hpq]; ring
  have h0 : (if (0:ℕ) = 0 then (0:ℝ) else if (0:ℕ) ≤ p then a else b)
      * Real.exp (-t * (if (0:ℕ) = 0 then (0:ℝ) else if (0:ℕ) ≤ p then a else b)) = 0 := by simp
  rw [h0, hA, hB]; ring

/-- **The band's relaxation value carries the ratio (the eigenvalue does NOT cancel).**
At the first scale's relaxation time `t = 1/a`, the running spectral dimension of the
two-scale band is a closed form in which the ratio `b/a` survives — contrast the single
cluster, where `a` cancels (`cluster_relaxation_formula`). -/
theorem twoCluster_relaxation_formula (a b : ℝ) (ha : a ≠ 0) (p q : ℕ) :
    runningSpectralDimension (p + q + 1) (twoClusterEigenvalues a b p q) (1 / a)
      = 2 * ((p : ℝ) * Real.exp (-1) + (q : ℝ) * (b / a) * Real.exp (-(b / a)))
          / (1 + (p : ℝ) * Real.exp (-1) + (q : ℝ) * Real.exp (-(b / a))) := by
  have hden : (1 : ℝ) + (p : ℝ) * Real.exp (-1) + (q : ℝ) * Real.exp (-(b / a)) ≠ 0 := by positivity
  have hN : ((p + q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have e1 : -(1 / a) * a = -1 := by rw [neg_mul, one_div, inv_mul_cancel₀ ha]
  have e2 : -(1 / a) * b = -(b / a) := by ring
  unfold runningSpectralDimension heatTraceDerivative heatTrace
  rw [twoCluster_sum_split, twoCluster_weighted_sum_split, e1, e2]
  field_simp

/-- Limiting macroscopic-band relaxation value as a function of the scale ratio `ρ`. -/
noncomputable def bandRelaxationLimit (ρ : ℝ) : ℝ :=
  2 * (Real.exp (-1) + ρ * Real.exp (-ρ)) / (Real.exp (-1) + Real.exp (-ρ))

/-- The band's limit minus 2, factored: the offset is set by the ratio. -/
theorem bandRelaxationLimit_offset (ρ : ℝ) :
    bandRelaxationLimit ρ - 2 = 2 * Real.exp (-ρ) * (ρ - 1) / (Real.exp (-1) + Real.exp (-ρ)) := by
  unfold bandRelaxationLimit
  have hd : Real.exp (-1) + Real.exp (-ρ) ≠ 0 := by positivity
  field_simp; ring

/-- **Class B sits off 2 exactly when the band has two genuinely distinct scales.**
The macroscopic-band relaxation value equals the convention-free `2` iff the two
scales coincide (`ρ = 1`); any genuine gap (`ρ ≠ 1`) pins it off 2. -/
theorem bandRelaxationLimit_eq_two_iff (ρ : ℝ) : bandRelaxationLimit ρ = 2 ↔ ρ = 1 := by
  rw [← sub_eq_zero, bandRelaxationLimit_offset]
  have hd : Real.exp (-1) + Real.exp (-ρ) ≠ 0 := by positivity
  have he : Real.exp (-ρ) ≠ 0 := Real.exp_ne_zero _
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · norm_num at h2
        · exact absurd h2 he
      · linarith
    · exact absurd h hd
  · intro h; left; rw [h]; ring

/-- **The macroscopic band (`p=q=r→∞`) tends to `L(b/a)`.** With
`bandRelaxationLimit_eq_two_iff`, a two-scale band lands on 2 iff its scales coincide;
a genuine gap reads off the universal line. -/
theorem twoCluster_relaxation_band_limit (a b : ℝ) (ha : a ≠ 0) :
    Tendsto (fun r : ℕ =>
        runningSpectralDimension (r + r + 1) (twoClusterEigenvalues a b r r) (1 / a))
      atTop (nhds (bandRelaxationLimit (b / a))) := by
  have hform : (fun r : ℕ => runningSpectralDimension (r + r + 1) (twoClusterEigenvalues a b r r) (1 / a))
      = (fun r : ℕ => 2 * ((r : ℝ) * Real.exp (-1) + (r : ℝ) * (b / a) * Real.exp (-(b / a)))
            / (1 + (r : ℝ) * Real.exp (-1) + (r : ℝ) * Real.exp (-(b / a)))) := by
    funext r; rw [twoCluster_relaxation_formula a b ha r r]
  rw [hform]
  have key : (fun r : ℕ => 2 * (Real.exp (-1) + (b / a) * Real.exp (-(b / a)))
        / ((1 / (r : ℝ)) + (Real.exp (-1) + Real.exp (-(b / a))))) =ᶠ[atTop]
      (fun r : ℕ => 2 * ((r : ℝ) * Real.exp (-1) + (r : ℝ) * (b / a) * Real.exp (-(b / a)))
            / (1 + (r : ℝ) * Real.exp (-1) + (r : ℝ) * Real.exp (-(b / a)))) := by
    filter_upwards [eventually_gt_atTop 0] with r hr
    have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hr)
    have hd1 : (1 / (r : ℝ)) + (Real.exp (-1) + Real.exp (-(b / a))) ≠ 0 := by positivity
    have hd2 : (1 : ℝ) + (r : ℝ) * Real.exp (-1) + (r : ℝ) * Real.exp (-(b / a)) ≠ 0 := by positivity
    field_simp
    ring
  refine Tendsto.congr' key ?_
  have hnum : Tendsto (fun _ : ℕ => 2 * (Real.exp (-1) + (b / a) * Real.exp (-(b / a))))
      atTop (nhds (2 * (Real.exp (-1) + (b / a) * Real.exp (-(b / a))))) := tendsto_const_nhds
  have hden : Tendsto (fun r : ℕ => (1 / (r : ℝ)) + (Real.exp (-1) + Real.exp (-(b / a))))
      atTop (nhds (0 + (Real.exp (-1) + Real.exp (-(b / a))))) := by
    apply Tendsto.add _ tendsto_const_nhds
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hd0 : (Real.exp (-1) + Real.exp (-(b / a))) ≠ 0 := by positivity
  have hlim := Tendsto.div hnum hden (by simpa using hd0)
  simpa [bandRelaxationLimit, zero_add] using hlim

end Verified.RelaxationTime
