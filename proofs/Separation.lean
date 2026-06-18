/-
Necessity witness for the separation criterion (rebuild) — machine-checked, 0 axioms.

HONEST SCOPE. This proves the WEAK necessity: for N ≥ 2 there exists a non-negative
eigenvalue sequence (the flat/zero sequence) that is NOT spectrally faithful w.r.t. the
complete-graph eigenvalues. It does NOT formalize Naor's dimension lower bound. Naor 2017
("A spectral gap precludes low-dimensional embeddings", SoCG 2017, arXiv:1611.08861) is the
physics MOTIVATION for why genuine bounded-gap emergence maps (expanders/trees) fail
faithfulness — it is NOT a theorem proved here.

This replaces the MMS-tree `naor_embedding_barrier` axiom, which the /research citation audit
(2026-06-15) showed was (i) MISLABELED — it never stated Naor's theorem; (ii) VACUOUS —
witnessed by `eigM ≡ 0`; and (iii) UNSOUND at N = 1 — K_1's only eigenvalue is 0, so the zero
sequence IS spectrally faithful and the existential is FALSE. The `2 ≤ N` hypothesis fixes the
soundness bug. (The MMS axiom carried no such hypothesis, so `naor_embedding_barrier 1` asserted
a falsehood.)
-/
import proofs.CompleteGraph

namespace Verified.Separation
open SpectralDimension

/-- Eigenvalue sandwich: `eigM` is spectrally faithful to `eigG` if uniformly comparable. -/
def SpectrallyFaithful {N : ℕ} (eigG eigM : Fin N → ℝ) : Prop :=
  ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧ ∀ k, c * eigG k ≤ eigM k ∧ eigM k ≤ C * eigG k

/-- **Weak necessity witness (corrected, proved, 0 axioms).** For `N ≥ 2`, the flat sequence
`eigM ≡ 0` is non-negative but NOT spectrally faithful w.r.t. the complete-graph eigenvalues:
at the index `k = 1` we have `λ_k(K_N) = N/(N-1) > 0`, so the lower sandwich `c·λ_k ≤ 0` fails
for every `c > 0`. (Naor 2017 motivates the strong obstruction; this is only the existence of a
non-faithful target — the honest content the old axiom actually had.) -/
theorem exists_not_spectrallyFaithful (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ (eigM : Fin N → ℝ), (∀ k, 0 ≤ eigM k) ∧
      ¬ SpectrallyFaithful (completeGraphEigenvalues N) eigM := by
  refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
  rintro ⟨c, _C, hc, _hC, hsand⟩
  have h1N : (1 : ℕ) < N := by omega
  have hk0 : (⟨1, h1N⟩ : Fin N) ≠ 0 := by intro h; simp [Fin.ext_iff] at h
  have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos1 : 0 < completeGraphEigenvalues N ⟨1, h1N⟩ := by
    simp only [completeGraphEigenvalues, if_neg hk0]
    exact div_pos (by linarith) (by linarith)
  have hlow : c * completeGraphEigenvalues N ⟨1, h1N⟩ ≤ 0 := (hsand ⟨1, h1N⟩).1
  linarith [mul_pos hc hpos1]

end Verified.Separation
