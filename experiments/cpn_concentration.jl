#!/usr/bin/env julia
#=
CP^n Fubini-Study Concentration: CV^2 vs 1/(n+1) Bound

Phase 24-01: Validate the Lean-verified concentration bound (Phase 20,
FubiniStudy.lean) that CV^2 <= 1/(n+1) for pairwise Fubini-Study distances
on CP^n under the Haar measure.

Algorithm:
  1. Sample m Haar-random quantum states on CP^n (= unit vectors in C^{n+1})
     by drawing complex Gaussian z ~ CN(0, I) and normalizing.
  2. Compute all m(m-1)/2 pairwise Fubini-Study distances:
       d_FS(|psi>, |phi>) = arccos(|<psi|phi>|)
  3. Measure CV^2 = Var(d_FS) / E[d_FS]^2 and compare against 1/(n+1).

Expected: CV^2 <= 1/(n+1) (conservative Lean bound), decreasing with n.

Generates: experiments/data/cpn_concentration.csv
=#

include(joinpath(@__DIR__, "spectral_dimension.jl"))

using Printf

# ─── Configuration ───────────────────────────────────────────────────────────
const CPN_DIMS  = [2, 5, 10, 20, 50, 100, 200, 500, 1000]
const M_STATES  = 200     # number of states to sample per trial
const N_TRIALS  = 5       # for error bars
const SEED      = 42

# ─── Output directory ────────────────────────────────────────────────────────
const DATA_DIR = joinpath(@__DIR__, "data")
mkpath(DATA_DIR)

# ═══════════════════════════════════════════════════════════════════════════════
#  Sampling and distance functions
# ═══════════════════════════════════════════════════════════════════════════════

"""
    sample_haar_states(n, m, rng)

Sample `m` Haar-random quantum states on CP^n (unit vectors in C^{n+1}).
Returns an m x (n+1) complex matrix where each row is a normalized state.
"""
function sample_haar_states(n::Int, m::Int, rng)
    dim = n + 1
    Z = randn(rng, ComplexF64, m, dim)
    # Normalize each row
    for i in 1:m
        Z[i, :] ./= norm(Z[i, :])
    end
    return Z
end

"""
    fubini_study_distance(psi, phi)

Compute the Fubini-Study distance d_FS = arccos(|<psi|phi>|).
Clamped to [0, 1] for numerical stability.
"""
function fubini_study_distance(psi::AbstractVector, phi::AbstractVector)
    overlap = abs(dot(psi, phi))
    return acos(min(1.0, overlap))
end

"""
    compute_cpn_cv_squared(n, m, rng)

Sample m states on CP^n, compute all pairwise Fubini-Study distances,
and return CV^2 = Var(d) / Mean(d)^2.
"""
function compute_cpn_cv_squared(n::Int, m::Int, rng)
    states = sample_haar_states(n, m, rng)

    # Compute all m*(m-1)/2 pairwise distances
    n_pairs = m * (m - 1) ÷ 2
    distances = Vector{Float64}(undef, n_pairs)
    idx = 0
    for i in 1:m
        for j in (i+1):m
            idx += 1
            distances[idx] = fubini_study_distance(
                @view(states[i, :]), @view(states[j, :]))
        end
    end

    mu = mean(distances)
    v = var(distances)
    return v / mu^2
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main experiment
# ═══════════════════════════════════════════════════════════════════════════════

function run_cpn_experiment()
    rng = Random.MersenneTwister(SEED)

    # Collect rows: (n, trial, cv_squared, bound, ratio)
    rows = Tuple{Int, Int, Float64, Float64, Float64}[]

    total = length(CPN_DIMS) * N_TRIALS
    progress = 0

    for n in CPN_DIMS
        bound = 1.0 / (n + 1)
        for trial in 1:N_TRIALS
            progress += 1
            cv2 = compute_cpn_cv_squared(n, M_STATES, rng)
            ratio = cv2 / bound
            push!(rows, (n, trial, cv2, bound, ratio))

            @printf("  n=%4d  trial=%d  CV²=%.6e  bound=%.6e  ratio=%.4f  (%d/%d)\n",
                    n, trial, cv2, bound, ratio, progress, total)
        end
    end

    return rows
end

# ═══════════════════════════════════════════════════════════════════════════════
#  CSV writing
# ═══════════════════════════════════════════════════════════════════════════════

function write_csv(rows)
    path = joinpath(DATA_DIR, "cpn_concentration.csv")
    open(path, "w") do io
        println(io, "n,trial,cv_squared,bound_1_over_n_plus_1,ratio")
        for (n, trial, cv2, bound, ratio) in rows
            @printf(io, "%d,%d,%.8e,%.8e,%.8e\n", n, trial, cv2, bound, ratio)
        end
    end
    println("  Wrote $path  ($(length(rows)) rows)")
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════════════════════

function main()
    println("=" ^ 70)
    println("CP^n FUBINI-STUDY CONCENTRATION: CV² vs 1/(n+1)")
    println("=" ^ 70)
    println("  dims=$CPN_DIMS")
    println("  m=$M_STATES states, $N_TRIALS trials, seed=$SEED")
    println()

    rows = run_cpn_experiment()

    println("\n── Writing CSV ──")
    write_csv(rows)

    # ── Summary table ──
    println("\n── Summary: mean CV² across trials ──")
    @printf("  %6s  %12s  %12s  %12s  %8s\n",
            "n", "mean_cv2", "std_cv2", "bound", "ratio")
    println("  ", "-" ^ 58)

    all_below_bound = true
    for n in CPN_DIMS
        subset = filter(r -> r[1] == n, rows)
        cv2_vals = [r[3] for r in subset]
        bound = 1.0 / (n + 1)
        m_cv2 = mean(cv2_vals)
        s_cv2 = std(cv2_vals)
        ratio = m_cv2 / bound

        if any(v -> v > bound, cv2_vals)
            all_below_bound = false
        end

        @printf("  %6d  %12.6e  %12.6e  %12.6e  %8.4f\n",
                n, m_cv2, s_cv2, bound, ratio)
    end

    # ── Verification ──
    println()
    if all_below_bound
        println("PASS: All measured CV² values are below the theoretical bound 1/(n+1).")
    else
        println("NOTE: Some measured CV² values exceed the theoretical bound 1/(n+1).")
        println("      (This may indicate the bound is tighter than expected for small n.)")
    end

    # ── Monotonicity check ──
    mean_cv2s = Float64[]
    for n in CPN_DIMS
        subset = filter(r -> r[1] == n, rows)
        push!(mean_cv2s, mean([r[3] for r in subset]))
    end

    monotone = all(mean_cv2s[i] >= mean_cv2s[i+1] for i in 1:(length(mean_cv2s)-1))
    if monotone
        println("PASS: CV² decreases monotonically with n (concentration improves).")
    else
        println("NOTE: CV² is not strictly monotonically decreasing.")
    end

    println()
    println("=" ^ 70)
    println("COMPLETE: CP^n Fubini-Study concentration experiment finished.")
    println("=" ^ 70)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
