#!/usr/bin/env julia
#=
Spectral Plateau Investigation

Does perturbing K_m (removing edges randomly) broaden the spectral density
enough to produce a D_S ≈ 2 plateau over a range of diffusion times t?

K_n has degenerate spectrum: λ₁=0, λ₂=...=λₙ = n/(n-1).
This gives D_S(t) = 2t (linear), so D_S = 2 only at t = 1.

Perturbing edges creates G(n, 1-p_remove), which should broaden the
eigenvalue distribution. If the broadened density has ρ(0) > 0 (like
a Wigner semicircle), then D_S(t) should plateau near 2 over [t₁, t₂].
=#

include("spectral_dimension.jl")

using Printf
using DelimitedFiles

"""
Build a perturbed complete graph: start with K_n and remove each edge
independently with probability p_remove. This gives G(n, 1-p_remove).
"""
function perturbed_complete_graph(n::Int, p_remove::Float64; rng=Random.default_rng())
    I_idx = Int[]
    J_idx = Int[]

    for i in 1:n
        for j in (i+1):n
            if rand(rng) > p_remove  # keep edge with probability 1 - p_remove
                push!(I_idx, i); push!(J_idx, j)
                push!(I_idx, j); push!(J_idx, i)
            end
        end
    end

    V = ones(length(I_idx))
    A = sparse(I_idx, J_idx, V, n, n)
    return A
end

"""
Compute D_S(t) curve for a single graph from its eigenvalues.
Returns (t_values, DS_values, P_values).
"""
function ds_curve(eigenvalues::Vector{Float64};
                  t_min=0.01, t_max=100.0, n_points=200)
    t_values = exp.(range(log(t_min), log(t_max), length=n_points))
    P_values = heat_trace_curve(eigenvalues, t_values)
    t_mid, DS_values = spectral_dimension_running(t_values, P_values)
    return t_mid, DS_values, P_values
end

"""
Measure plateau: find the range of t where |D_S(t) - 2| < tolerance.
Returns (t_low, t_high, width_ratio) where width_ratio = t_high/t_low.
"""
function measure_plateau(t_mid::Vector{Float64}, DS_values::Vector{Float64};
                         tolerance=0.2)
    in_plateau = abs.(DS_values .- 2.0) .< tolerance
    if !any(in_plateau)
        return NaN, NaN, 0.0
    end

    indices = findall(in_plateau)
    t_low = t_mid[first(indices)]
    t_high = t_mid[last(indices)]
    width_ratio = t_high / t_low

    return t_low, t_high, width_ratio
end

function run_plateau_experiment(;
        ns = [100, 200, 500],
        p_removes = [0.0, 0.01, 0.05, 0.10, 0.20],
        n_trials = 5,
        seed = 42)

    rng = Random.MersenneTwister(seed)

    # CSV output for D_S(t) curves
    ds_rows = []
    # CSV output for eigenvalue densities
    eig_rows = []

    total = length(ns) * length(p_removes) * n_trials
    count = 0

    println("="^60)
    println("SPECTRAL PLATEAU INVESTIGATION")
    println("="^60)
    println()

    for n in ns
        for p_remove in p_removes
            plateau_widths = Float64[]

            for trial in 1:n_trials
                count += 1
                print("\rProgress: $count / $total (n=$n, p=$p_remove, trial=$trial)    ")

                # Build graph
                if p_remove == 0.0
                    A = complete_graph(n)
                else
                    A = perturbed_complete_graph(n, p_remove; rng=rng)
                end

                # Ensure connected (extract LCC if needed)
                is_conn, _ = graph_connectivity(A)
                if !is_conn
                    A, _ = largest_connected_component(A)
                end

                # Compute spectrum
                L = normalized_laplacian(A)
                eigenvalues = compute_eigenvalues(L)

                # D_S(t) curve
                t_mid, DS_values, P_values = ds_curve(eigenvalues)

                # Record D_S curve data (subsample for CSV size)
                for (i, idx) in enumerate(1:4:length(t_mid))
                    push!(ds_rows, (n, p_remove, trial, t_mid[idx], DS_values[idx],
                                    i <= length(P_values) ? P_values[min(idx, length(P_values))] : NaN))
                end

                # Record eigenvalue density
                for λ in eigenvalues
                    push!(eig_rows, (n, p_remove, trial, λ))
                end

                # Measure plateau
                _, _, width = measure_plateau(t_mid, DS_values; tolerance=0.2)
                push!(plateau_widths, width)
            end

            mean_width = mean(plateau_widths)
            @printf("\n  n=%d, p_remove=%.2f: mean plateau width ratio = %.2f\n",
                    n, p_remove, mean_width)
        end
    end
    println()

    # Write CSVs
    mkpath("experiments/data")

    open("experiments/data/spectral_plateau.csv", "w") do f
        println(f, "n,p_remove,trial,t,DS_t,P_t")
        for row in ds_rows
            @printf(f, "%d,%.4f,%d,%.6e,%.6e,%.6e\n", row...)
        end
    end

    open("experiments/data/eigenvalue_density.csv", "w") do f
        println(f, "n,p_remove,trial,lambda")
        for row in eig_rows
            @printf(f, "%d,%.4f,%d,%.6e\n", row...)
        end
    end

    println("\nCSVs written:")
    println("  experiments/data/spectral_plateau.csv")
    println("  experiments/data/eigenvalue_density.csv")

    # Summary analysis
    println("\n" * "="^60)
    println("PLATEAU ANALYSIS SUMMARY")
    println("="^60)

    println("\nPlateau width ratio (t_high/t_low where |D_S - 2| < 0.2):")
    println("  Wider = more plateau-like behavior")
    println()

    # Header
    print("       p |")
    for n in ns
        print("   n=$n  |")
    end
    println()
    println("-"^(10 + 10 * length(ns)))

    for p_remove in p_removes
        @printf("   %.2f |", p_remove)
        for n in ns
            # Recompute summary from stored data
            widths = Float64[]
            for trial in 1:n_trials
                rng2 = Random.MersenneTwister(seed + hash((n, p_remove, trial)))
                if p_remove == 0.0
                    A = complete_graph(n)
                else
                    A = perturbed_complete_graph(n, p_remove; rng=rng2)
                end
                is_conn, _ = graph_connectivity(A)
                if !is_conn
                    A, _ = largest_connected_component(A)
                end
                L = normalized_laplacian(A)
                eigs = compute_eigenvalues(L)
                t_m, ds_v, _ = ds_curve(eigs)
                _, _, w = measure_plateau(t_m, ds_v; tolerance=0.2)
                push!(widths, w)
            end
            @printf("  %6.2f |", mean(widths))
        end
        println()
    end

    # D_S at specific t values for comparison
    println("\n\nD_S at key diffusion times (n=500, averaged over $n_trials trials):")
    println("-"^60)
    @printf("       p |  t=0.5  |  t=1.0  |  t=2.0  |  t=5.0  |\n")
    println("-"^60)

    for p_remove in p_removes
        @printf("   %.2f |", p_remove)
        ds_at_t = Dict(0.5 => Float64[], 1.0 => Float64[],
                        2.0 => Float64[], 5.0 => Float64[])
        for trial in 1:n_trials
            rng2 = Random.MersenneTwister(seed + hash((500, p_remove, trial)))
            if p_remove == 0.0
                A = complete_graph(500)
            else
                A = perturbed_complete_graph(500, p_remove; rng=rng2)
            end
            is_conn, _ = graph_connectivity(A)
            if !is_conn
                A, _ = largest_connected_component(A)
            end
            L = normalized_laplacian(A)
            eigs = compute_eigenvalues(L)
            t_m, ds_v, _ = ds_curve(eigs)
            for t_target in [0.5, 1.0, 2.0, 5.0]
                idx = argmin(abs.(t_m .- t_target))
                push!(ds_at_t[t_target], ds_v[idx])
            end
        end
        for t_target in [0.5, 1.0, 2.0, 5.0]
            @printf("  %5.3f  |", mean(ds_at_t[t_target]))
        end
        println()
    end
end

# Complete graph helper (same as in complete_graph_verification.jl)
function complete_graph(n::Int)
    A = ones(n, n) - I(n)
    return sparse(A)
end

if abspath(PROGRAM_FILE) == @__FILE__
    run_plateau_experiment()
end
