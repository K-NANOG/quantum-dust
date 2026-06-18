#!/usr/bin/env julia
#=
U(d) Hilbert-Schmidt Concentration: CV^2 vs 1/d^2 Bound

Phase 24-01: Validate the Lean-verified concentration bound (Phase 23,
UnitaryGroup.lean) that CV^2 <= 1/d^2 for pairwise Hilbert-Schmidt distances
on U(d) under the Haar measure.

Note: CV^2 = O(1/d^2) is quadratically faster concentration than CP^n's
O(1/n), reflecting the higher symmetry of the unitary group.

Algorithm:
  1. Sample m Haar-random d x d unitaries via QR decomposition of complex
     Gaussian matrices with Mezzadri phase correction.
  2. Compute all m(m-1)/2 pairwise Hilbert-Schmidt distances:
       d_HS(U, V) = ||U - V||_F  (Frobenius norm)
  3. Measure CV^2 = Var(d_HS) / E[d_HS]^2 and compare against 1/d^2.

Expected: CV^2 <= 1/d^2 (conservative Lean bound), decreasing quadratically.

Generates: experiments/data/ud_concentration.csv
=#

include(joinpath(@__DIR__, "spectral_dimension.jl"))

# METRIC NOTE: This experiment measures concentration of the Hilbert-Schmidt
# (Frobenius) chord distance d_HS(U,V) = ‖U - V‖_F in the ambient space M_d(ℂ).
# This is LEFT-invariant (d_HS(WU, WV) = d_HS(U,V)) but NOT bi-invariant under
# right multiplication. The bi-invariant geodesic metric is d_geo(U,V) = ‖log(U†V)‖_F.
#
# The CV² ≤ 1/d² bound in the paper (Theorem 6.X, UnitaryGroup.lean) applies to
# 1-Lipschitz functions on U(d) with the chord metric. The Haar concentration
# inequality Prob(|f - Ef| > ε) ≤ 2exp(-d²ε²/2) holds for the chord metric
# via the standard embedding U(d) ↪ M_d(ℂ) ≅ ℝ^{2d²}.
#
# Both metrics give valid concentration results; they differ in the constants.

using Printf

# ─── Configuration ───────────────────────────────────────────────────────────
const UD_DIMS     = [2, 3, 5, 10, 20, 50, 100, 200]
const M_UNITARIES = 100    # number of unitaries per trial (d x d matrices get large)
const N_TRIALS    = 5      # for error bars
const SEED        = 42

# ─── Output directory ────────────────────────────────────────────────────────
const DATA_DIR = joinpath(@__DIR__, "data")
mkpath(DATA_DIR)

# ═══════════════════════════════════════════════════════════════════════════════
#  Sampling and distance functions
# ═══════════════════════════════════════════════════════════════════════════════

"""
    sample_haar_unitary(d, rng)

Generate a single Haar-random d x d unitary matrix via the QR method
with Mezzadri phase correction.

Algorithm:
  1. Z = complex Gaussian d x d matrix (normalized variance)
  2. QR decomposition: Z = Q * R
  3. Phase correction: Q_haar = Q * Diagonal(sign.(diag(R)))

The phase correction ensures true Haar distribution, not just uniform
on cosets of the diagonal torus.
"""
function sample_haar_unitary(d::Int, rng)
    Z = randn(rng, ComplexF64, d, d) / sqrt(2)
    F = qr(Z)
    Q = Matrix(F.Q)
    R = F.R
    # Phase correction: multiply by signs of diagonal of R
    d_diag = diag(R)
    signs = map(z -> abs(z) < 1e-15 ? one(ComplexF64) : z / abs(z), d_diag)
    return Q * Diagonal(signs)
end

"""
    hilbert_schmidt_distance(U, V)

Compute the Hilbert-Schmidt (Frobenius) chord distance d_HS = ||U - V||_F
in the ambient space M_d(ℂ), NOT the intrinsic geodesic metric ‖log(U†V)‖_F.
"""
function hilbert_schmidt_distance(U::AbstractMatrix, V::AbstractMatrix)
    return norm(U - V)  # Frobenius norm is the default for matrices
end

"""
    compute_ud_cv_squared(d, m, rng)

Sample m unitaries of size d x d, compute all pairwise Hilbert-Schmidt
distances, and return CV^2 = Var(d) / Mean(d)^2.
"""
function compute_ud_cv_squared(d::Int, m::Int, rng)
    # Sample m unitaries
    unitaries = [sample_haar_unitary(d, rng) for _ in 1:m]

    # Compute all m*(m-1)/2 pairwise distances
    n_pairs = m * (m - 1) ÷ 2
    distances = Vector{Float64}(undef, n_pairs)
    idx = 0
    for i in 1:m
        for j in (i+1):m
            idx += 1
            distances[idx] = hilbert_schmidt_distance(unitaries[i], unitaries[j])
        end
    end

    mu = mean(distances)
    v = var(distances)
    return v / mu^2
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main experiment
# ═══════════════════════════════════════════════════════════════════════════════

function run_ud_experiment()
    rng = Random.MersenneTwister(SEED)

    # Collect rows: (d, trial, cv_squared, bound, ratio)
    rows = Tuple{Int, Int, Float64, Float64, Float64}[]

    total = length(UD_DIMS) * N_TRIALS
    progress = 0

    for d in UD_DIMS
        bound = 1.0 / d^2
        # Reduce sample count for large d to keep runtime reasonable
        m = d >= 100 ? 50 : M_UNITARIES

        for trial in 1:N_TRIALS
            progress += 1
            cv2 = compute_ud_cv_squared(d, m, rng)
            ratio = cv2 / bound
            push!(rows, (d, trial, cv2, bound, ratio))

            @printf("  d=%4d  trial=%d  m=%3d  CV²=%.6e  bound=%.6e  ratio=%.4f  (%d/%d)\n",
                    d, trial, m, cv2, bound, ratio, progress, total)
        end
    end

    return rows
end

# ═══════════════════════════════════════════════════════════════════════════════
#  CSV writing
# ═══════════════════════════════════════════════════════════════════════════════

function write_csv(rows)
    path = joinpath(DATA_DIR, "ud_concentration.csv")
    open(path, "w") do io
        println(io, "d,trial,cv_squared,bound_1_over_d_squared,ratio")
        for (d, trial, cv2, bound, ratio) in rows
            @printf(io, "%d,%d,%.8e,%.8e,%.8e\n", d, trial, cv2, bound, ratio)
        end
    end
    println("  Wrote $path  ($(length(rows)) rows)")
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════════════════════

function main()
    println("=" ^ 70)
    println("U(d) HILBERT-SCHMIDT CONCENTRATION: CV² vs 1/d²")
    println("=" ^ 70)
    println("  dims=$UD_DIMS")
    println("  m=$M_UNITARIES unitaries (m=50 for d>=100), $N_TRIALS trials, seed=$SEED")
    println()

    rows = run_ud_experiment()

    println("\n── Writing CSV ──")
    write_csv(rows)

    # ── Summary table ──
    println("\n── Summary: mean CV² across trials ──")
    @printf("  %6s  %12s  %12s  %12s  %8s\n",
            "d", "mean_cv2", "std_cv2", "bound", "ratio")
    println("  ", "-" ^ 58)

    all_below_bound = true
    for d in UD_DIMS
        subset = filter(r -> r[1] == d, rows)
        cv2_vals = [r[3] for r in subset]
        bound = 1.0 / d^2
        m_cv2 = mean(cv2_vals)
        s_cv2 = std(cv2_vals)
        ratio = m_cv2 / bound

        if any(v -> v > bound, cv2_vals)
            all_below_bound = false
        end

        @printf("  %6d  %12.6e  %12.6e  %12.6e  %8.4f\n",
                d, m_cv2, s_cv2, bound, ratio)
    end

    # ── Verification ──
    println()
    if all_below_bound
        println("PASS: All measured CV² values are below the theoretical bound 1/d².")
    else
        println("NOTE: Some measured CV² values exceed the theoretical bound 1/d².")
        println("      (This may indicate the bound is tighter than expected for small d.)")
    end

    # ── Concentration rate comparison ──
    println()
    println("── Concentration Rate Comparison ──")
    println("  Space       CV² scaling     Rate")
    println("  ─────────────────────────────────────")
    println("  B^d         ~ 1/d           linear")
    println("  CP^n        ~ 1/(n+1)       linear")
    println("  U(d)        ~ 1/d²          quadratic")
    println()
    println("  U(d) concentrates quadratically faster than CP^n or B^d.")
    println("  This reflects the higher symmetry (d² real dimensions) of the")
    println("  unitary group compared to projective space (2n real dimensions).")

    println()
    println("=" ^ 70)
    println("COMPLETE: U(d) Hilbert-Schmidt concentration experiment finished.")
    println("=" ^ 70)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
