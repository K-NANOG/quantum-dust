#!/usr/bin/env python3
"""
CV^2 asymptotic for Fubini-Study concentration on CP^n  --  reproducible verification.

Definition (matches experiments/cpn_concentration.jl and the paper):
    d_FS(psi,phi) = arccos(|<psi|phi>|)
    CV^2(n)       = Var[d_FS] / E[d_FS]^2      (variance of the DISTANCE, not its square)

Result (derived + verified here):
    CV^2(n) = (4 - pi)/(pi^2 * n) + O(n^{-3/2}),   leading constant (4-pi)/pi^2 ~= 0.086975
    subleading:  CV^2(n) = (4-pi)/(pi^2 n) * (1 + 2/sqrt(pi*n) + ...)

Derivation:
    u := |<psi|phi>|^2 ~ Beta(1,n)  for Haar-random states in C^{n+1}.
    d_FS = arccos(sqrt(u)) = pi/2 - arcsin(sqrt(u)).
    E[u] = 1/(n+1);  E[sqrt u] = Gamma(3/2)Gamma(n+1)/Gamma(n+3/2) ~ (sqrt(pi)/2) n^{-1/2}.
    n->oo: E[d_FS] -> pi/2;  Var[d_FS] -> Var[sqrt u] = E[u]-E[sqrt u]^2 -> (4-pi)/(4n).
    => CV^2 -> [(4-pi)/(4n)] / (pi/2)^2 = (4-pi)/(pi^2 n).   (Watson's-lemma leading order)

Independent Monte-Carlo check (no numpy/scipy): sample u ~ Beta(1,n) by inverse-CDF
    u = 1 - (1-p)^{1/n},  p ~ U(0,1)        [ Beta(1,n) CDF = 1-(1-u)^n ].
NOTE: an earlier draft mis-stated the constant as ~0.35/n by computing Var[d^2]/E[d^2]^2
(the SQUARED distance); the code and paper use Var[d]/E[d]^2, for which (4-pi)/(pi^2 n) holds.
"""
import math, random


def mc_cv2(n, N=3_000_000, seed=1):
    rng = random.Random(seed)
    s1 = s2 = 0.0
    for _ in range(N):
        u = 1.0 - rng.random() ** (1.0 / n)        # u ~ Beta(1,n)
        d = math.acos(min(1.0, math.sqrt(u)))      # Fubini-Study distance
        s1 += d
        s2 += d * d
    e1, e2 = s1 / N, s2 / N
    return (e2 - e1 * e1) / (e1 * e1)


if __name__ == "__main__":
    C = (4 - math.pi) / math.pi ** 2
    print(f"leading constant (4-pi)/pi^2 = {C:.6f}\n")
    print(f"{'n':>6} {'CV2_MC':>13} {'pred=C/n':>13} {'n*CV2':>9} {'ratio':>8}")
    for n in [2, 5, 10, 20, 50, 100, 200, 500, 1000, 5000]:
        cv2 = mc_cv2(n)
        print(f"{n:>6} {cv2:>13.6e} {C / n:>13.6e} {n * cv2:>9.5f} {cv2 / (C / n):>8.4f}")
    print("\nExpected: n*CV2 descends monotonically to 0.086975; ratio -> 1.")
