/-
The reachable partial of the Monogamy-Lift frontier (Result #3) — machine-checked, 0 axioms.

HONEST SCOPE. This proves only the elementary arithmetic core of "monogamy forces thin threads":
if a vertex shares entanglement w_i ≥ 0 with each of its k neighbours and entanglement monogamy
bounds the total by 1 (∑ w_i ≤ 1 — the Coffman–Kundu–Wootters / Osborne–Verstraete inequality),
then at least one thread is thin, w_i ≤ 1/k. For a vertex of the equidistant complete graph K_m
this gives 1/(m−1) → 0: Fields' "narrow-bandwidth ER bridges".

It does NOT prove the bridge. The entanglement content (w_i = tangle, ∑ ≤ 1) is the CITED CKW /
Osborne–Verstraete theorem; the open conjecture (results_monogamy_frontier.md) is that Fubini–Study
equidistance MAKES the K_m edges such monogamous tangles in the first place.
-/
import Mathlib

namespace Verified.Monogamy
open Finset

/-- **Monogamy forces a thin thread (elementary core, 0 axioms).** The additive pigeonhole:
`∑ wᵢ ≤ 1` over `k` neighbours ⇒ some thread is thin, `wᵢ ≤ 1/k`. (Elegance note: nonnegativity
of the `wᵢ` is NOT needed — the monogamy sum bound alone forces it; this is literally
`Finset.exists_le_of_sum_le`, the additive pigeonhole.) -/
theorem monogamy_thin_threads (k : ℕ) (hk : 0 < k) (w : Fin k → ℝ)
    (hsum : ∑ i, w i ≤ 1) :
    ∃ i, w i ≤ 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have Hle : ∑ i : Fin k, w i ≤ ∑ _i : Fin k, (1 / (k : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div, div_self hk'.ne']
    exact hsum
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne Hle
  exact ⟨i, hi⟩

end Verified.Monogamy
