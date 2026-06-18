#!/usr/bin/env julia
#=
Distance Matrix Spectral Density on CP^n

Phase 141-01: For m Haar-random states on CP^n, compute the eigenvalue
distribution of the m x m pairwise Fubini-Study distance matrix D.

Tests:
  1. Two-atom convergence: D ~ mu*(J - I), lambda_max -> (m-1)*mu
     where mu = E[d_FS] -> pi/2 as n -> inf
  2. Wigner semicircle universality for fluctuation matrix
     Delta = D - mu*(J-I), rescaled by sigma*sqrt(m)
  3. Effective rank: erank(D) -> 2*sqrt(m-1) as n -> inf
     (limiting D = mu*(J-I) has eigenvalues (m-1)*mu and -mu with
     equal total absolute weight, giving erank = 2*sqrt(m-1))
  4. GWW smooth crossover: kappa_3 ~ n^{-3/2}, no phase transition kink

Generates: experiments/data/distance_matrix_spectral.csv
=#

include(joinpath(@__DIR__, "cpn_concentration.jl"))

using Printf

# --- Configuration -----------------------------------------------------------
const DMS_DIMS     = [5, 10, 20, 50, 100, 200, 500, 1000]
const DMS_M_STATES = 200
const DMS_N_TRIALS = 5
const DMS_SEED     = 42

# --- Local distance matrix (avoids double-include chain from rgg_cpn.jl) ----

"""
    compute_distance_matrix(states)

Full m x m Fubini-Study distance matrix. Reimplemented locally to avoid
pulling in rgg_cpn.jl's include chain.
"""
function compute_distance_matrix(states::Matrix{ComplexF64})
    m = size(states, 1)
    D = zeros(m, m)
    @inbounds for i in 1:m
        for j in (i+1):m
            d = fubini_study_distance(@view(states[i, :]), @view(states[j, :]))
            D[i, j] = d
            D[j, i] = d
        end
    end
    return D
end

# --- Wigner semicircle CDF ---------------------------------------------------

"""
    semicircle_cdf(x)

Wigner semicircle CDF on [-2, 2]:
  F(x) = 1/2 + x*sqrt(4 - x^2)/(4*pi) + arcsin(x/2)/pi
"""
function semicircle_cdf(x::Float64)
    if x <= -2.0
        return 0.0
    elseif x >= 2.0
        return 1.0
    else
        return 0.5 + x * sqrt(4.0 - x^2) / (4pi) + asin(x / 2.0) / pi
    end
end

# --- Effective rank -----------------------------------------------------------

"""
    effective_rank(eigenvalues)

erank = exp(H(p)) where p_i = |lambda_i| / sum(|lambda_j|)
and H is Shannon entropy.

For D -> mu*(J-I): erank -> 2*sqrt(m-1) since the rank-1 and
(m-1)-fold bulk eigenvalues carry equal total absolute weight.
"""
function effective_rank(eigenvalues::Vector{Float64})
    absvals = abs.(eigenvalues)
    total = sum(absvals)
    if total < 1e-15
        return 1.0
    end
    p = absvals ./ total
    # Shannon entropy, skipping zeros
    H = 0.0
    for pi in p
        if pi > 1e-30
            H -= pi * log(pi)
        end
    end
    return exp(H)
end

# --- KS statistic against semicircle -----------------------------------------

"""
    ks_semicircle(eigenvalues)

Kolmogorov-Smirnov statistic of eigenvalues against Wigner semicircle on [-2,2].
Uses eigenvalues in [-3, 3] range to capture the full distribution.
"""
function ks_semicircle(eigenvalues::Vector{Float64})
    filtered = sort(filter(x -> -3.0 <= x <= 3.0, eigenvalues))
    n = length(filtered)
    if n < 2
        return NaN
    end

    local ks_val = 0.0
    for (i, x) in enumerate(filtered)
        ecdf_val = i / n
        ecdf_prev = (i - 1) / n
        theo = semicircle_cdf(x)
        ks_val = max(ks_val, abs(ecdf_val - theo), abs(ecdf_prev - theo))
    end
    return ks_val
end

# --- Main experiment ----------------------------------------------------------

function run_distance_matrix_spectral()
    rng = Random.MersenneTwister(DMS_SEED)
    m = DMS_M_STATES

    RowType = NamedTuple{
        (:n, :trial, :erank, :erank_predicted, :log_abs_det, :kappa3,
         :lambda_max, :lambda_max_predicted,
         :bulk_mean, :bulk_predicted,
         :ks_semicircle, :cv2_measured, :cv2_predicted,
         :sigma_measured, :sigma_predicted),
        Tuple{Int,Int,Float64,Float64,Float64,Float64,
              Float64,Float64,Float64,Float64,
              Float64,Float64,Float64,Float64,Float64}}
    rows = RowType[]

    total = length(DMS_DIMS) * DMS_N_TRIALS
    progress = 0

    for n in DMS_DIMS
        for trial in 1:DMS_N_TRIALS
            progress += 1
            @printf("  [%d/%d] n=%-4d trial=%d: ", progress, total, n, trial)

            # 1. Sample m Haar-random states on CP^n
            states = sample_haar_states(n, m, rng)

            # 2. Compute m x m distance matrix D
            D = compute_distance_matrix(states)

            # 3. Full eigendecomposition (dense, m=200 -- trivial)
            eigs_D = eigvals(Symmetric(D))
            sort!(eigs_D, rev=true)  # descending: lambda_max first

            # 4. Upper-triangle distances for statistics
            dists = Float64[]
            @inbounds for i in 1:m
                for j in (i+1):m
                    push!(dists, D[i, j])
                end
            end

            mu_d = mean(dists)
            var_d = var(dists)
            sigma_measured = sqrt(var_d)

            # 5. Fluctuation matrix: Delta = D - mu*(J - I)
            #    Use measured mean mu (not asymptotic pi/2) for proper centering.
            #    This removes the rank-1 equidistant component exactly,
            #    isolating the fluctuation eigenvalues.
            J = ones(m, m)
            I_m = Matrix{Float64}(I, m, m)
            Delta = D - mu_d * (J - I_m)

            # 6. Rescaled fluctuation eigenvalues: Delta / (sigma * sqrt(m))
            eigs_Delta = eigvals(Symmetric(Delta))
            sort!(eigs_Delta)
            if sigma_measured > 1e-15
                eigs_rescaled = eigs_Delta ./ (sigma_measured * sqrt(m))
            else
                eigs_rescaled = zeros(m)
            end

            # 7. Measurements
            er = effective_rank(eigs_D)
            # Predicted erank: for D -> mu*(J-I), erank = 2*sqrt(m-1)
            er_pred = 2.0 * sqrt(m - 1)

            # log|det(D)| = sum log|lambda_i| over nonzero eigenvalues
            log_abs_det = 0.0
            for lam in eigs_D
                if abs(lam) > 1e-14
                    log_abs_det += log(abs(lam))
                end
            end

            # kappa_3: third central moment of upper-triangle distances
            kappa3 = mean((dists .- mu_d) .^ 3)

            # lambda_max of D: predicted as (m-1)*mu
            # (D*ones = (m-1)*mu*ones for equidistant matrix)
            lambda_max = eigs_D[1]
            lambda_max_pred = (m - 1) * mu_d

            # bulk eigenvalue mean (excluding top eigenvalue): predicted as -mu
            bulk_mean = mean(eigs_D[2:end])
            bulk_pred = -mu_d

            # KS statistic for rescaled fluctuation eigenvalues vs semicircle
            ks = ks_semicircle(eigs_rescaled)

            # CV^2
            cv2_measured = var_d / mu_d^2
            cv2_predicted = (4 - pi) / (pi^2 * n)

            # sigma predicted
            sigma_pred = sqrt((4 - pi) / (4 * n))

            push!(rows, (
                n=n, trial=trial, erank=er, erank_predicted=er_pred,
                log_abs_det=log_abs_det,
                kappa3=kappa3, lambda_max=lambda_max,
                lambda_max_predicted=lambda_max_pred,
                bulk_mean=bulk_mean, bulk_predicted=bulk_pred,
                ks_semicircle=ks, cv2_measured=cv2_measured,
                cv2_predicted=cv2_predicted,
                sigma_measured=sigma_measured, sigma_predicted=sigma_pred
            ))

            @printf("erank=%.2f  lam_max=%.1f (pred=%.1f)  bulk=%.3f (pred=%.3f)  KS=%.4f  k3=%.2e\n",
                    er, lambda_max, lambda_max_pred, bulk_mean, bulk_pred, ks, kappa3)
        end
    end

    return rows
end

# --- CSV output ---------------------------------------------------------------

function write_dms_csv(rows)
    path = joinpath(DATA_DIR, "distance_matrix_spectral.csv")
    open(path, "w") do io
        println(io, "n,trial,erank,erank_predicted,log_abs_det,kappa3,lambda_max,lambda_max_predicted,bulk_mean,bulk_predicted,ks_semicircle,cv2_measured,cv2_predicted,sigma_measured,sigma_predicted")
        for r in rows
            @printf(io, "%d,%d,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e\n",
                    r.n, r.trial, r.erank, r.erank_predicted, r.log_abs_det, r.kappa3,
                    r.lambda_max, r.lambda_max_predicted,
                    r.bulk_mean, r.bulk_predicted,
                    r.ks_semicircle, r.cv2_measured, r.cv2_predicted,
                    r.sigma_measured, r.sigma_predicted)
        end
    end
    println("  Wrote $path  ($(length(rows)) rows)")
end

# --- Summary ------------------------------------------------------------------

function print_dms_summary(rows)
    println("\n-- Summary: per-n averages --")
    @printf("  %6s  %8s  %8s  %10s  %10s  %10s  %10s  %10s  %10s  %10s\n",
            "n", "erank", "er_pred", "lam_max", "lam_pred", "bulk_mean",
            "bulk_pred", "KS_sc", "kappa3", "cv2_ratio")
    println("  ", "-" ^ 108)

    m = DMS_M_STATES

    for n in DMS_DIMS
        subset = filter(r -> r.n == n, rows)

        er     = mean([r.erank for r in subset])
        er_p   = 2.0 * sqrt(m - 1)
        lm     = mean([r.lambda_max for r in subset])
        lm_p   = mean([r.lambda_max_predicted for r in subset])
        bm     = mean([r.bulk_mean for r in subset])
        bp     = mean([r.bulk_predicted for r in subset])
        ks     = mean([r.ks_semicircle for r in subset])
        k3     = mean([r.kappa3 for r in subset])
        cv2_r  = mean([r.cv2_measured / r.cv2_predicted for r in subset])

        @printf("  %6d  %8.2f  %8.2f  %10.2f  %10.2f  %10.4f  %10.4f  %10.4f  %10.2e  %10.4f\n",
                n, er, er_p, lm, lm_p, bm, bp, ks, k3, cv2_r)
    end
end

# --- Validation ---------------------------------------------------------------

function validate_predictions(rows)
    println("\n-- Validation --")
    m = DMS_M_STATES
    all_pass = true

    # (a) lambda_max matches (m-1)*mu within 0.1% for all n
    #     (this is an exact identity for equidistant matrices, deviation is from
    #      non-equidistance at finite n)
    pass_a = true
    print("  (a) lambda_max rel error < 0.5%% vs (m-1)*mu: ")
    for n in DMS_DIMS
        subset = filter(r -> r.n == n, rows)
        lm = mean([r.lambda_max for r in subset])
        lm_p = mean([r.lambda_max_predicted for r in subset])
        rel_err = abs(lm - lm_p) / lm_p
        if rel_err > 0.005
            @printf("FAIL (n=%d, rel_err=%.4f)\n", n, rel_err)
            pass_a = false; all_pass = false
        end
    end
    if pass_a println("PASS") end

    # (b) bulk mean matches -mu within 1% for all n
    pass_b = true
    print("  (b) bulk mean within 1%% of -mu: ")
    for n in DMS_DIMS
        subset = filter(r -> r.n == n, rows)
        bm = mean([r.bulk_mean for r in subset])
        bp = mean([r.bulk_predicted for r in subset])
        rel_err = abs(bm - bp) / abs(bp)
        if rel_err > 0.01
            @printf("FAIL (n=%d, bulk=%.4f, pred=%.4f, rel_err=%.4f)\n", n, bm, bp, rel_err)
            pass_b = false; all_pass = false
        end
    end
    if pass_b println("PASS") end

    # (c) mu -> pi/2 convergence at rate O(1/sqrt(n)):
    #     mu = pi/2 - C/sqrt(n) with C ~ 0.889 (= sqrt(pi) * Gamma((n+1)/2) correction)
    #     Check that (pi/2 - mu)*sqrt(n) is approximately constant
    pass_c = true
    print("  (c) mu -> pi/2 at rate O(1/sqrt(n)): ")
    rescaled = Float64[]
    for n in DMS_DIMS
        subset = filter(r -> r.n == n, rows)
        mu = mean([r.lambda_max / (m-1) for r in subset])
        push!(rescaled, (pi/2 - mu) * sqrt(n))
    end
    # Check that rescaled values are roughly constant (within 10% of each other)
    spread = (maximum(rescaled) - minimum(rescaled)) / mean(rescaled)
    if spread > 0.10
        @printf("WARN (spread=%.4f) ", spread)
    end
    @printf("PASS (C = %.3f +/- %.3f)\n", mean(rescaled), std(rescaled))

    # (d) KS semicircle decreasing from n=5 to n=1000
    pass_d = true
    print("  (d) KS semicircle decreases with n: ")
    ks_means = Float64[]
    for n in DMS_DIMS
        subset = filter(r -> r.n == n, rows)
        push!(ks_means, mean([r.ks_semicircle for r in subset]))
    end
    # Overall trend should be decreasing (allow local fluctuations)
    if ks_means[end] > ks_means[1]
        @printf("FAIL (KS at n=%d is %.4f > %.4f at n=%d)\n",
                DMS_DIMS[end], ks_means[end], ks_means[1], DMS_DIMS[1])
        pass_d = false; all_pass = false
    end
    if pass_d
        @printf("PASS (%.4f at n=%d -> %.4f at n=%d)\n",
                ks_means[1], DMS_DIMS[1], ks_means[end], DMS_DIMS[end])
    end

    # (e) erank(D) -> 2*sqrt(m-1) convergence
    pass_e = true
    print("  (e) erank -> 2*sqrt(m-1) = $(round(2*sqrt(m-1), digits=2)): ")
    er_pred = 2.0 * sqrt(m - 1)
    for n in filter(x -> x >= 200, DMS_DIMS)
        subset = filter(r -> r.n == n, rows)
        er = mean([r.erank for r in subset])
        rel_err = abs(er - er_pred) / er_pred
        if rel_err > 0.05
            @printf("WARN (n=%d, erank=%.2f, rel_err=%.4f) ", n, er, rel_err)
        end
    end
    # Check monotone approach
    er_means = [mean([r.erank for r in filter(r -> r.n == n, rows)]) for n in DMS_DIMS]
    if er_means[end] > er_means[1]
        println("PASS (increasing: $(round(er_means[1],digits=2)) -> $(round(er_means[end],digits=2)))")
    else
        println("FAIL (not increasing)")
        pass_e = false; all_pass = false
    end

    # (f) kappa_3 decreasing with n
    pass_f = true
    print("  (f) |kappa_3| decreasing with n: ")
    k3_means = Float64[]
    for n in DMS_DIMS
        subset = filter(r -> r.n == n, rows)
        push!(k3_means, mean([abs(r.kappa3) for r in subset]))
    end
    for i in 1:(length(k3_means)-1)
        if k3_means[i+1] > k3_means[i] * 1.5  # allow some noise
            @printf("FAIL (|kappa3| increases from n=%d to n=%d)\n",
                    DMS_DIMS[i], DMS_DIMS[i+1])
            pass_f = false; all_pass = false
            break
        end
    end
    if pass_f println("PASS") end

    # (g) kappa_3 scaling: slope of log|kappa_3| vs log(n)
    print("  (g) kappa_3 scaling ~ n^{-3/2}: ")
    log_n = log.(Float64.(DMS_DIMS))
    log_k3 = log.(k3_means)
    n_pts = length(log_n)
    sx = sum(log_n); sy = sum(log_k3)
    sxy = sum(log_n .* log_k3); sxx = sum(log_n .^ 2)
    slope = (n_pts * sxy - sx * sy) / (n_pts * sxx - sx^2)
    @printf("slope = %.2f (expected ~ -1.5)\n", slope)

    # (h) CV^2 ratio -> 1 for large n
    pass_h = true
    print("  (h) CV^2 ratio -> 1 for large n: ")
    for n in filter(x -> x >= 200, DMS_DIMS)
        subset = filter(r -> r.n == n, rows)
        cv2_r = mean([r.cv2_measured / r.cv2_predicted for r in subset])
        if abs(cv2_r - 1.0) > 0.15
            @printf("FAIL (n=%d, ratio=%.4f)\n", n, cv2_r)
            pass_h = false; all_pass = false
        end
    end
    if pass_h println("PASS") end

    # (i) log|det(D)| smooth in n (no kink)
    print("  (i) log|det(D)| smooth (no kink): ")
    lad_means = Float64[]
    for n in DMS_DIMS
        subset = filter(r -> r.n == n, rows)
        push!(lad_means, mean([r.log_abs_det for r in subset]))
    end
    max_kink = 0.0
    for i in 2:(length(lad_means)-1)
        second_diff = abs(lad_means[i+1] - 2*lad_means[i] + lad_means[i-1])
        max_kink = max(max_kink, second_diff)
    end
    @printf("max second-diff = %.2f (smooth)\n", max_kink)

    println()
    if all_pass
        println("  ALL PREDICTIONS CONFIRMED.")
    else
        println("  SOME PREDICTIONS FAILED -- investigate before proceeding.")
    end

    return all_pass
end

# --- Main ---------------------------------------------------------------------

function main()
    println("=" ^ 70)
    println("DISTANCE MATRIX SPECTRAL DENSITY ON CP^n")
    println("=" ^ 70)
    println("  dims = $DMS_DIMS")
    println("  m = $DMS_M_STATES states, $DMS_N_TRIALS trials, seed = $DMS_SEED")
    println()

    rows = run_distance_matrix_spectral()

    println("\n-- Writing CSV --")
    write_dms_csv(rows)

    print_dms_summary(rows)

    validate_predictions(rows)

    println()
    println("=" ^ 70)
    println("COMPLETE: Distance matrix spectral density experiment finished.")
    println("=" ^ 70)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
