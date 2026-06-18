#!/usr/bin/env julia
#=
Random Geometric Graphs on CP^n: D_S Crossover from Geometric to Foam Regime

Phase 140-01: Build ε-graphs on CP^n from Haar-random states, compute
normalized Laplacian spectral dimension D_S(1), and measure the crossover:
  D_S ~ 2n (geometric regime, small ε) → 2 (foam/K_m regime, large ε)
as ε crosses the concentration threshold.

Algorithm:
  1. Sample m Haar-random states on CP^n
  2. Compute all m(m-1)/2 pairwise Fubini-Study distances
  3. For each threshold ε: build binary adjacency A_ij = 1{d_ij ≤ ε}
  4. Compute D_S(1) = 2·Σ λ_i e^{-λ_i} / Σ e^{-λ_i} from normalized Laplacian
  5. Measure foam metrics: CV², max deviation, edge fraction

Generates: experiments/data/rgg_cpn.csv
=#

include(joinpath(@__DIR__, "cpn_concentration.jl"))

using Printf

# ─── Configuration ───────────────────────────────────────────────────────────
const RGG_CPN_DIMS   = [5, 10, 20, 50, 100, 200, 500]
const RGG_M_STATES   = 200
const RGG_N_TRIALS   = 5
const RGG_SEED       = 42
const RGG_N_EPS      = 30

# ═══════════════════════════════════════════════════════════════════════════════
#  ε-graph construction
# ═══════════════════════════════════════════════════════════════════════════════

"""
    compute_fs_distance_matrix(states)

Compute all m(m-1)/2 pairwise Fubini-Study distances.
Returns full symmetric m×m distance matrix with zero diagonal.
"""
function compute_fs_distance_matrix(states::Matrix{ComplexF64})
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

"""
    build_eps_graph(dist_matrix, eps)

Construct sparse binary adjacency: A_ij = 1 if d_ij ≤ ε.
Returns (A, mean_degree, edge_fraction).
"""
function build_eps_graph(dist_matrix::Matrix{Float64}, eps::Float64)
    m = size(dist_matrix, 1)
    I_idx = Int[]
    J_idx = Int[]

    @inbounds for i in 1:m
        for j in (i+1):m
            if dist_matrix[i, j] <= eps
                push!(I_idx, i); push!(J_idx, j)
                push!(I_idx, j); push!(J_idx, i)
            end
        end
    end

    V = ones(length(I_idx))
    A = sparse(I_idx, J_idx, V, m, m)

    n_edges = length(I_idx) ÷ 2
    max_edges = m * (m - 1) ÷ 2
    edge_fraction = n_edges / max_edges
    mean_degree = length(I_idx) > 0 ? mean(vec(sum(A, dims=2))) : 0.0

    return A, mean_degree, edge_fraction
end

# ═══════════════════════════════════════════════════════════════════════════════
#  D_S at t=1 via direct eigenvalue formula
# ═══════════════════════════════════════════════════════════════════════════════

"""
    compute_ds_at_t1(A)

Compute D_S(t=1) from the normalized Laplacian of A.
For disconnected graphs, extracts the largest connected component.

D_S(1) = 2·Σ λ_i·e^{-λ_i} / Σ e^{-λ_i}

Returns (ds_t1, lcc_fraction, spectral_gap, n_eigenvalues).
"""
function compute_ds_at_t1(A::SparseMatrixCSC)
    m = size(A, 1)

    # Handle trivial cases
    if nnz(A) == 0
        return (NaN, 0.0, 0.0, 0)
    end

    # Check connectivity and extract LCC if needed
    is_conn, _ = graph_connectivity(A)
    if !is_conn
        A_lcc, lcc_idx = largest_connected_component(A)
        lcc_fraction = length(lcc_idx) / m
        # Need at least 2 vertices in LCC
        if length(lcc_idx) < 2
            return (NaN, lcc_fraction, 0.0, length(lcc_idx))
        end
    else
        A_lcc = A
        lcc_fraction = 1.0
    end

    n_lcc = size(A_lcc, 1)

    # Normalized Laplacian
    L = normalized_laplacian(A_lcc)

    # Full eigendecomposition (m ≤ 500)
    eigenvalues = compute_eigenvalues(L)

    # Spectral gap
    spectral_gap = length(eigenvalues) >= 2 ? eigenvalues[2] : 0.0

    # D_S(1) = 2·Σ λ_i·e^{-λ_i} / Σ e^{-λ_i}
    exp_neg_lam = exp.(-eigenvalues)
    numerator = sum(eigenvalues .* exp_neg_lam)
    denominator = sum(exp_neg_lam)

    ds_t1 = denominator > 0 ? 2.0 * numerator / denominator : NaN

    return (ds_t1, lcc_fraction, spectral_gap, n_lcc)
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Foam metrics
# ═══════════════════════════════════════════════════════════════════════════════

"""
    compute_foam_metrics(dist_matrix, n)

Measure foam structure: CV², max deviation from mean, predicted CV².
"""
function compute_foam_metrics(dist_matrix::Matrix{Float64}, n::Int)
    m = size(dist_matrix, 1)

    # Extract upper-triangle distances
    distances = Float64[]
    @inbounds for i in 1:m
        for j in (i+1):m
            push!(distances, dist_matrix[i, j])
        end
    end

    mean_dist = mean(distances)
    var_dist = var(distances)
    cv2_measured = var_dist / mean_dist^2

    # Analytical prediction: CV²(CP^n) ~ (4-π)/(π²·n)
    cv2_predicted = (4 - π) / (π^2 * n)

    # Max deviation: max_{i<j} |d_ij - E[D]| / E[D]
    max_deviation = maximum(abs.(distances .- mean_dist)) / mean_dist

    return (mean_dist, max_deviation, cv2_measured, cv2_predicted)
end

# ═══════════════════════════════════════════════════════════════════════════════
#  D_S(K_m, 1) analytical baseline
# ═══════════════════════════════════════════════════════════════════════════════

"""
    ds_km_analytical(m)

Exact D_S(K_m, t=1) = 2m·e^{-m/(m-1)} / (1 + (m-1)·e^{-m/(m-1)}).
"""
function ds_km_analytical(m::Int)
    λ = m / (m - 1)
    e_neg_λ = exp(-λ)
    return 2m * e_neg_λ / (1 + (m - 1) * e_neg_λ)
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main sweep
# ═══════════════════════════════════════════════════════════════════════════════

function run_rgg_cpn_experiment()
    rng = Random.MersenneTwister(RGG_SEED)

    # ε values: linearly spaced from 0.05 to π/2
    eps_values = range(0.05, π/2, length=RGG_N_EPS)

    # D_S(K_m, 1) baseline
    ds_km = ds_km_analytical(RGG_M_STATES)
    @printf("  D_S(K_%d, 1) analytical = %.4f\n\n", RGG_M_STATES, ds_km)

    # CSV rows (typed for Julia inference)
    RowType = NamedTuple{(:n,:eps,:trial,:ds_t1,:ds_km_analytical,:edge_fraction,:mean_degree,:lcc_fraction,:max_deviation,:cv2_measured,:cv2_predicted,:spectral_gap),
                         Tuple{Int,Float64,Int,Float64,Float64,Float64,Float64,Float64,Float64,Float64,Float64,Float64}}
    rows = RowType[]

    total = length(RGG_CPN_DIMS) * RGG_N_TRIALS
    progress = 0

    for n in RGG_CPN_DIMS
        for trial in 1:RGG_N_TRIALS
            progress += 1
            @printf("  [%d/%d] n=%d, trial=%d: sampling... ", progress, total, n, trial)

            # Sample states once per (n, trial), sweep ε
            states = sample_haar_states(n, RGG_M_STATES, rng)
            dist_matrix = compute_fs_distance_matrix(states)

            # Foam metrics (independent of ε)
            mean_dist, max_dev, cv2_m, cv2_p = compute_foam_metrics(dist_matrix, n)

            @printf("CV²=%.4e (pred=%.4e, ratio=%.2f)\n", cv2_m, cv2_p, cv2_m/cv2_p)

            for (ei, eps) in enumerate(eps_values)
                A, mean_deg, edge_frac = build_eps_graph(dist_matrix, eps)
                ds_t1, lcc_frac, spec_gap, n_eig = compute_ds_at_t1(A)

                push!(rows, (
                    n=n, eps=eps, trial=trial,
                    ds_t1=ds_t1, ds_km_analytical=ds_km,
                    edge_fraction=edge_frac, mean_degree=mean_deg,
                    lcc_fraction=lcc_frac, max_deviation=max_dev,
                    cv2_measured=cv2_m, cv2_predicted=cv2_p,
                    spectral_gap=spec_gap
                ))
            end
        end
    end

    return rows, eps_values
end

# ═══════════════════════════════════════════════════════════════════════════════
#  CSV output
# ═══════════════════════════════════════════════════════════════════════════════

function write_rgg_csv(rows)
    path = joinpath(DATA_DIR, "rgg_cpn.csv")
    open(path, "w") do io
        println(io, "n,eps,trial,ds_t1,ds_km_analytical,edge_fraction,mean_degree,lcc_fraction,max_deviation,cv2_measured,cv2_predicted,spectral_gap")
        for r in rows
            @printf(io, "%d,%.8e,%d,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e\n",
                    r.n, r.eps, r.trial, r.ds_t1, r.ds_km_analytical,
                    r.edge_fraction, r.mean_degree, r.lcc_fraction,
                    r.max_deviation, r.cv2_measured, r.cv2_predicted, r.spectral_gap)
        end
    end
    println("  Wrote $path  ($(length(rows)) rows)")
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Summary
# ═══════════════════════════════════════════════════════════════════════════════

function print_rgg_summary(rows, eps_values)
    println("\n── Summary ──")
    println()

    ds_km = ds_km_analytical(RGG_M_STATES)

    @printf("  %-6s  %-12s  %-12s  %-12s  %-10s  %-10s  %-10s\n",
            "n", "D_S(small_ε)", "D_S(large_ε)", "D_S(K_m)", "foam_onset_ε", "CV²_ratio", "max_dev")
    println("  ", "-" ^ 80)

    for n in RGG_CPN_DIMS
        n_rows = filter(r -> r.n == n, rows)

        # Mean D_S at smallest ε (geometric)
        small_eps_rows = filter(r -> r.eps ≈ first(eps_values), n_rows)
        ds_small = mean([r.ds_t1 for r in small_eps_rows if !isnan(r.ds_t1)])

        # Mean D_S at largest ε (foam)
        large_eps_rows = filter(r -> r.eps ≈ last(eps_values), n_rows)
        ds_large = mean([r.ds_t1 for r in large_eps_rows if !isnan(r.ds_t1)])

        # Foam onset: first ε where mean D_S < 2.5
        foam_onset = NaN
        for eps in eps_values
            eps_rows = filter(r -> r.eps ≈ eps && !isnan(r.ds_t1), n_rows)
            if !isempty(eps_rows)
                ds_mean = mean([r.ds_t1 for r in eps_rows])
                if ds_mean < 2.5
                    foam_onset = eps
                    break
                end
            end
        end

        # CV² ratio (same across ε)
        cv2_ratio = n_rows[1].cv2_measured / n_rows[1].cv2_predicted
        max_dev = n_rows[1].max_deviation

        ds_small_str = isnan(ds_small) ? "disconn" : @sprintf("%.3f", ds_small)
        ds_large_str = isnan(ds_large) ? "disconn" : @sprintf("%.3f", ds_large)
        foam_str = isnan(foam_onset) ? "never" : @sprintf("%.3f", foam_onset)

        @printf("  %-6d  %-12s  %-12s  %-12.3f  %-10s  %-10.3f  %-10.4f\n",
                n, ds_small_str, ds_large_str, ds_km, foam_str, cv2_ratio, max_dev)
    end

    # Edge fraction at ε = π/2
    println("\n── Edge fraction at ε = π/2 (should be 1.0 for all n) ──")
    for n in RGG_CPN_DIMS
        large_eps_rows = filter(r -> r.n == n && r.eps ≈ last(eps_values), rows)
        ef = mean([r.edge_fraction for r in large_eps_rows])
        @printf("  n=%-4d  edge_fraction=%.4f\n", n, ef)
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════════════════════

function main()
    println("=" ^ 70)
    println("RANDOM GEOMETRIC GRAPHS ON CP^n: D_S CROSSOVER")
    println("=" ^ 70)
    println("  dims = $RGG_CPN_DIMS")
    println("  m = $RGG_M_STATES states, $RGG_N_TRIALS trials, seed = $RGG_SEED")
    println("  ε range: 0.05 to π/2 ≈ $(round(π/2, digits=4)), $RGG_N_EPS values")
    println()

    rows, eps_values = run_rgg_cpn_experiment()

    println("\n── Writing CSV ──")
    write_rgg_csv(rows)

    print_rgg_summary(rows, eps_values)

    println()
    println("=" ^ 70)
    println("COMPLETE: RGG on CP^n D_S crossover experiment finished.")
    println("=" ^ 70)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
