/-
Axiom audit for the Verified (rebuild) library.
Build this module and read the printed axiom sets: a genuinely-proved result must
depend on NOTHING beyond Lean's three foundational axioms
  [propext, Classical.choice, Quot.sound]
and in particular must show NO `sorryAx` and NONE of the MMS-tree physics axioms.
-/
import Verified.CompleteGraph
import Verified.Concentration
import Verified.Separation
import Verified.UniversalValue
import Verified.Monogamy
import Verified.RelaxationTime
import Verified.Stability
import Verified.Transfer
import Verified.PowerLaw
import Verified.BetaMoments
import Verified.EmpiricalCollapse

-- L3: K_m has running spectral dimension D_S(1) -> 2 as m -> infinity.
#print axioms SpectralDimension.completeGraph_spectralDimension_two
#print axioms SpectralDimension.spectralDimension_quantitative

-- L2: empirical Chebyshev / union bound (concentration core).
#print axioms Verified.count_sqdev_mul_le
#print axioms Verified.chebyshev_count

-- Separation necessity (corrected + de-axiomatized replacement for `naor_embedding_barrier`).
#print axioms Verified.Separation.exists_not_spectrallyFaithful

-- The composed Universal Kinematic Value: eigenvalues → K_m  ⇒  D_S(1) → 2.
#print axioms Verified.UniversalValue.universal_value

-- Monogamy-lift frontier, reachable partial: monogamy forces a thin thread.
#print axioms Verified.Monogamy.monogamy_thin_threads

-- Convention-free relaxation-time crossing: D_S(cluster a, 1/a) -> 2 (a cancels).
#print axioms Verified.RelaxationTime.cluster_relaxation_formula
#print axioms Verified.RelaxationTime.cluster_spectralDimension_relaxation_two

-- Full separation-gap limit: D_S(cluster a, 1) -> 2a (the limit half of the gap theorem).
#print axioms Verified.RelaxationTime.cluster_fixedclock_formula
#print axioms Verified.RelaxationTime.cluster_spectralDimension_fixed_two_a

-- Class B (two-scale band): the relaxation value carries the ratio rho=b/a (the
-- eigenvalue does NOT cancel), and the macroscopic-band limit L(rho) = 2 iff rho = 1
-- -- the formal root of a gapped, multiply-scaled spectrum lying off the universal line.
#print axioms Verified.RelaxationTime.twoCluster_relaxation_formula
#print axioms Verified.RelaxationTime.bandRelaxationLimit_offset
#print axioms Verified.RelaxationTime.bandRelaxationLimit_eq_two_iff
#print axioms Verified.RelaxationTime.twoCluster_relaxation_band_limit

-- Stability spine (perturbation -> D_S stability), audited explicitly.
#print axioms Stability.exp_neg_mul_lipschitz
#print axioms Stability.heatTrace_perturbation_bound
#print axioms Stability.heatTraceDerivative_perturbation_bound
#print axioms Stability.spectralDimension_stability

-- Faithfulness-transfer, unconditional half (Theorem IV.4): the sandwich forces the
-- heat-trace squeeze, and the squeeze transfers the scaling exponent. The regular-variation
-- plateau half is page-proved (Karamata / monotone-density, not in Mathlib).
#print axioms Verified.Transfer.heatTrace_faithful_squeeze
#print axioms Verified.Transfer.exponent_transfer

-- Exact power-law plateau (Theorem IV.4, regular-variation half — EXACT special case): the
-- power-law heat trace Θ(t) = A·Γ(1+d/2)·t^{-d/2} (scaled Gamma integral), and the running
-- spectral dimension D_S(t) = -2t·Θ'/Θ = d EXACTLY for every t>0, no limit, no Tauberian input.
-- The slowly-varying generalization N(λ)=λ^{d/2}ℓ(λ) needs Karamata + monotone-density (not in
-- Mathlib) and stays a page proof.
#print axioms Verified.PowerLaw.heatTrace_powerLaw
#print axioms Verified.PowerLaw.running_dimension_of_closedForm
#print axioms Verified.PowerLaw.powerLaw_spectralDimension

-- Exact finite-n polynomial moments of the Beta(1, m+1) squared-overlap law (Proposition II.1):
-- E[u] = 1/(n+1) and E[u²] = 2/((n+1)(n+2)) with n = m+1, by explicit antiderivatives. The
-- half-integer moment E[√u] and the (4-π)/(π²n) asymptotic remain page proofs (Complex-only Beta).
#print axioms Verified.BetaMoments.integral_u_mul_one_sub_pow
#print axioms Verified.BetaMoments.beta_first_moment
#print axioms Verified.BetaMoments.integral_u_sq_mul_one_sub_pow
#print axioms Verified.BetaMoments.beta_second_moment

-- Population → empirical bridge (the new step closing the gap in cor:floor). The marginal Beta(1,n)
-- tail P(u>x)=(1-x)^n; the deterministic uniform collapse of a bounded sample (variance ≤ ε²,
-- empirical CV² ≤ ε²/(c-ε)², every edge retained); and the union-bound bridge concluding that an
-- ACTUAL sample's empirical variance exceeds ε² (resp. its thresholded graph is not K_m) only with
-- probability ≤ C(m,2)·q. Boole over the fixed C(m,2) pairs: no independence assumed.
#print axioms Verified.BetaMoments.beta_tail
#print axioms Verified.mean_mem_Icc
#print axioms Verified.variance_le_sq_of_mem_Icc
#print axioms Verified.cv_sq_le_of_mem_Icc
#print axioms Verified.edges_retained_of_mem_Icc
#print axioms Verified.EmpiricalCollapse.bad_event_le
#print axioms Verified.EmpiricalCollapse.empirical_collapse
#print axioms Verified.EmpiricalCollapse.complete_graph_whp
