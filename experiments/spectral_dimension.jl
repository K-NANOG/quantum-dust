#!/usr/bin/env julia
#=
Spectral Dimension of Random Geometric Graphs in High Dimensions

This module computes the spectral dimension D_S of random geometric graphs
as the ambient dimension d grows, testing whether concentration of measure
produces the D_S → 2 phenomenon observed in quantum gravity.

The spectral dimension measures how a random walker "sees" effective dimensionality:
  P(t) ~ t^{-D_S/2}  →  D_S = -2 · d(log P)/d(log t)
=#

using LinearAlgebra
using SparseArrays
using Statistics
using Random

#=============================================================================
  Step 1: Sampling Points from Unit Ball in R^d

  Algorithm:
  1. Sample x ~ N(0, I_d) (d-dimensional standard normal)
  2. Normalize to unit sphere: x̂ = x / ||x||
  3. Sample radial factor: r = u^{1/d} where u ~ Uniform(0,1)
  4. Return r * x̂
=============================================================================#

"""
    sample_unit_ball(n::Int, d::Int; rng=Random.default_rng())

Sample `n` points uniformly from the unit ball in `d` dimensions.
Returns an n × d matrix where each row is a point.
"""
function sample_unit_ball(n::Int, d::Int; rng=Random.default_rng())
    # Sample from d-dimensional standard normal
    points = randn(rng, n, d)

    # Normalize each row to unit length (project to sphere)
    norms = sqrt.(sum(points.^2, dims=2))
    points ./= norms

    # Sample radial factors: r = u^{1/d} for uniform interior
    u = rand(rng, n)
    r = u.^(1/d)

    # Scale each point by its radial factor
    points .*= r

    return points
end

"""
    verify_sampling_2d(n::Int=1000)

Verify sampling visually in 2D (returns points for plotting).
"""
function verify_sampling_2d(n::Int=1000)
    points = sample_unit_ball(n, 2)
    # Check: distances from origin should have CDF ≈ r² on [0,1]
    radii = sqrt.(sum(points.^2, dims=2))[:]
    println("Radial distribution check (should be uniform on [0,1]²):")
    println("  Mean radius: $(mean(radii)) (expected: 2/3 ≈ 0.667)")
    println("  Median radius: $(median(radii)) (expected: 1/√2 ≈ 0.707)")
    return points
end

#=============================================================================
  Step 2: Building the Random Geometric Graph

  Connect points if distance ≤ ε. The choice of ε must adapt to dimension
  due to concentration of measure (distances concentrate around √(2d/(d+2)) → √2).

  Strategy: Set ε as a percentile of the pairwise distance distribution
  to maintain approximately constant average degree.
=============================================================================#

"""
    pairwise_distances(points::Matrix{Float64})

Compute all pairwise Euclidean distances. Returns n × n matrix.
For large n, this is O(n²d) in time and O(n²) in space.
"""
function pairwise_distances(points::Matrix{Float64})
    n = size(points, 1)
    dists = zeros(n, n)

    @inbounds for i in 1:n
        for j in (i+1):n
            d = 0.0
            for k in 1:size(points, 2)
                d += (points[i,k] - points[j,k])^2
            end
            d = sqrt(d)
            dists[i,j] = d
            dists[j,i] = d
        end
    end

    return dists
end

"""
    build_geometric_graph(points::Matrix{Float64};
                          target_degree::Int=10,
                          percentile::Union{Nothing,Float64}=nothing)

Build a random geometric graph connecting points within distance ε.

If `percentile` is given (e.g., 0.05 for 5th percentile), use that percentile
of the pairwise distance distribution as ε.

Otherwise, adaptively choose ε to achieve approximately `target_degree`
expected neighbors per vertex.

Returns: (adjacency matrix as sparse, chosen ε, actual mean degree)
"""
function build_geometric_graph(points::Matrix{Float64};
                               target_degree::Int=10,
                               percentile::Union{Nothing,Float64}=nothing)
    n = size(points, 1)
    dists = pairwise_distances(points)

    # Extract upper triangle distances (excluding diagonal)
    upper_dists = Float64[]
    for i in 1:n
        for j in (i+1):n
            push!(upper_dists, dists[i,j])
        end
    end
    sort!(upper_dists)

    if percentile !== nothing
        # Use given percentile
        idx = max(1, ceil(Int, percentile * length(upper_dists)))
        ε = upper_dists[idx]
    else
        # Adaptive: target_degree neighbors means connecting to
        # fraction target_degree/(n-1) of other vertices
        # So we want ε at percentile target_degree/(n-1)
        frac = target_degree / (n - 1)
        idx = max(1, ceil(Int, frac * length(upper_dists)))
        ε = upper_dists[min(idx, length(upper_dists))]
    end

    # Build sparse adjacency matrix
    I_idx = Int[]
    J_idx = Int[]

    for i in 1:n
        for j in (i+1):n
            if dists[i,j] ≤ ε
                push!(I_idx, i); push!(J_idx, j)
                push!(I_idx, j); push!(J_idx, i)
            end
        end
    end

    V = ones(length(I_idx))
    A = sparse(I_idx, J_idx, V, n, n)

    mean_degree = mean(sum(A, dims=2))

    return A, ε, mean_degree
end

"""
    ensure_connected(A::SparseMatrixCSC)

Check if graph is connected via BFS. Returns (is_connected, largest_component_size).
"""
function graph_connectivity(A::SparseMatrixCSC)
    n = size(A, 1)
    visited = falses(n)

    # BFS from vertex 1
    queue = [1]
    visited[1] = true
    component_size = 0

    while !isempty(queue)
        v = popfirst!(queue)
        component_size += 1

        # Get neighbors
        for j in findnz(A[v, :])[1]
            if !visited[j]
                visited[j] = true
                push!(queue, j)
            end
        end
    end

    return component_size == n, component_size
end

#=============================================================================
  Step 3: Computing the Graph Laplacian

  Combinatorial Laplacian: L = D - A
  Normalized Laplacian: L_norm = I - D^{-1/2} A D^{-1/2}

  For spectral dimension, we use the normalized Laplacian.
=============================================================================#

"""
    normalized_laplacian(A::SparseMatrixCSC)

Compute the normalized Laplacian L = I - D^{-1/2} A D^{-1/2}.
Returns a sparse matrix.

Handles isolated vertices (degree 0) by treating them as self-loops.
"""
function normalized_laplacian(A::SparseMatrixCSC)
    n = size(A, 1)

    # Degree vector
    degrees = vec(sum(A, dims=2))

    # Handle isolated vertices: set degree to 1 to avoid division by zero
    degrees[degrees .== 0] .= 1

    # D^{-1/2}
    D_inv_sqrt = Diagonal(1.0 ./ sqrt.(degrees))

    # Normalized adjacency
    A_norm = D_inv_sqrt * A * D_inv_sqrt

    # L = I - A_norm
    L = sparse(I, n, n) - A_norm

    return L
end

"""
    combinatorial_laplacian(A::SparseMatrixCSC)

Compute the combinatorial Laplacian L = D - A.
"""
function combinatorial_laplacian(A::SparseMatrixCSC)
    degrees = vec(sum(A, dims=2))
    D = Diagonal(degrees)
    return D - A
end

#=============================================================================
  Step 4: Computing the Heat Trace (Return Probability)

  P(t) = (1/n) Tr(exp(-tL)) = (1/n) Σᵢ exp(-t λᵢ)

  where {λᵢ} are eigenvalues of the normalized Laplacian.
=============================================================================#

"""
    compute_eigenvalues(L::SparseMatrixCSC; full::Bool=true)

Compute eigenvalues of the Laplacian.
If full=true, compute all eigenvalues (for n < 2000).
Otherwise, compute smallest k eigenvalues using iterative methods.
"""
function compute_eigenvalues(L; full::Bool=true)
    if full
        # Convert to dense for full eigendecomposition
        eigenvalues = eigvals(Symmetric(Matrix(L)))
        # Ensure non-negative (numerical errors can give tiny negatives)
        eigenvalues = max.(eigenvalues, 0.0)
        return sort(eigenvalues)
    else
        # For large matrices, use iterative methods (Arpack)
        # This would require Arpack.jl
        error("Iterative eigenvalue computation not implemented")
    end
end

"""
    heat_trace(eigenvalues::Vector{Float64}, t::Float64)

Compute the heat trace P(t) = (1/n) Σᵢ exp(-t λᵢ).
"""
function heat_trace(eigenvalues::Vector{Float64}, t::Float64)
    return mean(exp.(-t .* eigenvalues))
end

"""
    heat_trace_curve(eigenvalues::Vector{Float64},
                     t_values::Vector{Float64})

Compute P(t) for a range of t values.
"""
function heat_trace_curve(eigenvalues::Vector{Float64},
                          t_values::Vector{Float64})
    return [heat_trace(eigenvalues, t) for t in t_values]
end

#=============================================================================
  Step 5: Extracting Spectral Dimension

  D_S = -2 · d(log P)/d(log t)

  This can be computed as a running dimension D_S(t) or as an asymptotic value.
=============================================================================#

"""
    spectral_dimension_running(t_values::Vector{Float64},
                               P_values::Vector{Float64})

Compute the running spectral dimension D_S(t) from the local slope.
Returns (t_mid, D_S) where t_mid are the midpoints between t values.
"""
function spectral_dimension_running(t_values::Vector{Float64},
                                    P_values::Vector{Float64})
    log_t = log.(t_values)
    log_P = log.(P_values)

    # Numerical derivative: D_S = -2 * Δ(log P) / Δ(log t)
    n = length(t_values)
    t_mid = Float64[]
    D_S = Float64[]

    for i in 1:(n-1)
        push!(t_mid, exp((log_t[i] + log_t[i+1]) / 2))
        slope = (log_P[i+1] - log_P[i]) / (log_t[i+1] - log_t[i])
        push!(D_S, -2 * slope)
    end

    return t_mid, D_S
end

"""
    spectral_dimension_asymptotic(t_values::Vector{Float64},
                                  P_values::Vector{Float64};
                                  use_range::Tuple{Float64,Float64}=(10.0, Inf))

Extract asymptotic spectral dimension from large-t behavior.
Fits a line to log P vs log t in the specified range.
"""
function spectral_dimension_asymptotic(t_values::Vector{Float64},
                                       P_values::Vector{Float64};
                                       use_range::Tuple{Float64,Float64}=(10.0, Inf))
    @warn "spectral_dimension_asymptotic uses power-law regression on log-log data, which is invalid for dense/complete graphs where P(t) → 1/n. Use spectral_dimension_running at a specific t instead." maxlog=1

    # Filter to range
    mask = (t_values .≥ use_range[1]) .& (t_values .≤ use_range[2])

    if sum(mask) < 2
        # Not enough points, use all
        mask = trues(length(t_values))
    end

    log_t = log.(t_values[mask])
    log_P = log.(P_values[mask])

    # Linear regression: log_P = a + b * log_t
    # D_S = -2 * b
    n = length(log_t)
    sum_x = sum(log_t)
    sum_y = sum(log_P)
    sum_xy = sum(log_t .* log_P)
    sum_xx = sum(log_t .* log_t)

    b = (n * sum_xy - sum_x * sum_y) / (n * sum_xx - sum_x^2)

    return -2 * b
end

#=============================================================================
  Step 5b: Largest Connected Component Extraction
=============================================================================#

"""
    find_components(A::SparseMatrixCSC)

Find all connected components via BFS. Returns vector of component label per vertex.
"""
function find_components(A::SparseMatrixCSC)
    n = size(A, 1)
    labels = zeros(Int, n)
    comp_id = 0

    for start in 1:n
        labels[start] != 0 && continue
        comp_id += 1
        queue = [start]
        labels[start] = comp_id
        while !isempty(queue)
            v = popfirst!(queue)
            rows = rowvals(A)
            for idx in nzrange(A, v)
                j = rows[idx]
                if labels[j] == 0
                    labels[j] = comp_id
                    push!(queue, j)
                end
            end
        end
    end
    return labels
end

"""
    largest_connected_component(A::SparseMatrixCSC)

Extract the largest connected component subgraph.
Returns (A_sub, indices) where A_sub is the adjacency of the LCC.
"""
function largest_connected_component(A::SparseMatrixCSC)
    labels = find_components(A)
    max_label = maximum(labels)
    sizes = [count(==(c), labels) for c in 1:max_label]
    best = argmax(sizes)
    indices = findall(==(best), labels)
    A_sub = A[indices, indices]
    return A_sub, indices
end

#=============================================================================
  Step 6: The Full Experiment
=============================================================================#

"""
    single_trial(n::Int, d::Int;
                 target_degree::Int=10,
                 t_range::Tuple{Float64,Float64}=(0.1, 1000.0),
                 n_t_points::Int=50,
                 rng=Random.default_rng())

Run a single trial: sample points, build graph, compute spectral dimension.

Returns a NamedTuple with results.
"""
function single_trial(n::Int, d::Int;
                      target_degree::Int=10,
                      t_range::Tuple{Float64,Float64}=(0.1, 1000.0),
                      n_t_points::Int=50,
                      rng=Random.default_rng())

    # Step 1: Sample points
    points = sample_unit_ball(n, d; rng=rng)

    # Step 2: Build graph
    A, ε, mean_deg = build_geometric_graph(points; target_degree=target_degree)

    # Check connectivity
    is_connected, largest_cc = graph_connectivity(A)

    # Extract LCC for disconnected graphs
    if !is_connected
        A_lcc, lcc_indices = largest_connected_component(A)
        lcc_fraction = length(lcc_indices) / n
    else
        A_lcc = A
        lcc_fraction = 1.0
    end

    # Step 3: Compute Laplacian (on LCC to avoid disconnected components)
    L = normalized_laplacian(A_lcc)

    # Step 4: Eigenvalues and heat trace
    eigenvalues = compute_eigenvalues(L)

    # Time values on log scale
    t_values = exp.(range(log(t_range[1]), log(t_range[2]), length=n_t_points))
    P_values = heat_trace_curve(eigenvalues, t_values)

    # Step 5: Spectral dimension
    t_mid, D_S_running = spectral_dimension_running(t_values, P_values)
    D_S_asymptotic = spectral_dimension_asymptotic(t_values, P_values)

    # Pointwise D_S at t=1 (preferred over asymptotic for dense graphs)
    idx_t1 = argmin(abs.(t_mid .- 1.0))
    D_S_t1 = D_S_running[idx_t1]

    return (
        n = n,
        d = d,
        epsilon = ε,
        mean_degree = mean_deg,
        is_connected = is_connected,
        largest_cc = largest_cc,
        lcc_fraction = lcc_fraction,
        eigenvalues = eigenvalues,
        t_values = t_values,
        P_values = P_values,
        t_mid = t_mid,
        D_S_running = D_S_running,
        D_S_asymptotic = D_S_asymptotic,
        D_S_t1 = D_S_t1
    )
end

"""
    run_experiment(;
        dimensions = [3, 10, 30, 100],
        sample_sizes = [200, 500, 1000],
        num_trials = 5,
        target_degree = 10,
        seed = 42)

Run the full experiment sweeping over dimensions and sample sizes.
"""
function run_experiment(;
        dimensions = [3, 10, 30, 100],
        sample_sizes = [200, 500, 1000],
        num_trials = 5,
        target_degree = 10,
        seed = 42)

    rng = Random.MersenneTwister(seed)

    results = []

    total = length(dimensions) * length(sample_sizes) * num_trials
    count = 0

    for d in dimensions
        for n in sample_sizes
            D_S_trials = Float64[]

            for trial in 1:num_trials
                count += 1
                print("\rProgress: $count / $total (d=$d, n=$n, trial=$trial)    ")

                result = single_trial(n, d; target_degree=target_degree, rng=rng)
                push!(D_S_trials, result.D_S_t1)
            end

            D_S_mean = mean(D_S_trials)
            D_S_std = std(D_S_trials)

            push!(results, (
                d = d,
                n = n,
                D_S_mean = D_S_mean,
                D_S_std = D_S_std,
                D_S_trials = D_S_trials
            ))
        end
    end
    println()

    return results
end

"""
    print_results(results)

Pretty-print experiment results.
"""
function print_results(results)
    println("\n" * "="^60)
    println("SPECTRAL DIMENSION OF RANDOM GEOMETRIC GRAPHS")
    println("="^60)
    println()

    # Group by dimension
    dims = unique([r.d for r in results])
    ns = unique([r.n for r in results])

    # Header
    print("     d  |")
    for n in ns
        print("   n=$n   |")
    end
    println()
    println("-"^(8 + 12 * length(ns)))

    for d in dims
        print("   $(lpad(d, 3)) |")
        for n in ns
            r = filter(x -> x.d == d && x.n == n, results)[1]
            print(" $(lpad(round(r.D_S_mean, digits=2), 5)) ± $(lpad(round(r.D_S_std, digits=2), 4)) |")
        end
        println()
    end

    println()
    println("If D_S → 2 as d → ∞, concentration of measure produces")
    println("the dimensional reduction seen in quantum gravity.")
end

#=============================================================================
  Verification and Testing
=============================================================================#

"""
    verify_on_lattice(n_side::Int=10, d::Int=2)

Verify on a d-dimensional lattice, where D_S should equal d.
"""
function verify_on_lattice(n_side::Int=10, d::Int=2)
    # Build d-dimensional lattice graph
    if d == 1
        # Path graph
        n = n_side
        A = spzeros(n, n)
        for i in 1:(n-1)
            A[i, i+1] = 1
            A[i+1, i] = 1
        end
    elseif d == 2
        # 2D grid
        n = n_side^2
        A = spzeros(n, n)
        for i in 1:n_side
            for j in 1:n_side
                idx = (i-1)*n_side + j
                # Right neighbor
                if j < n_side
                    A[idx, idx+1] = 1
                    A[idx+1, idx] = 1
                end
                # Down neighbor
                if i < n_side
                    A[idx, idx+n_side] = 1
                    A[idx+n_side, idx] = 1
                end
            end
        end
    else
        error("Lattice verification only implemented for d=1,2")
    end

    L = normalized_laplacian(A)
    eigenvalues = compute_eigenvalues(L)

    t_values = exp.(range(log(0.1), log(100.0), length=30))
    P_values = heat_trace_curve(eigenvalues, t_values)

    D_S = spectral_dimension_asymptotic(t_values, P_values; use_range=(1.0, 50.0))

    println("Lattice verification (d=$d):")
    println("  Expected D_S ≈ $d")
    println("  Computed D_S = $(round(D_S, digits=3))")

    return D_S
end

"""
    detailed_analysis(n::Int, d::Int; target_degree::Int=10, seed::Int=42)

Run a detailed analysis for a single (n, d) configuration.
Prints diagnostic information and returns full results.
"""
function detailed_analysis(n::Int, d::Int; target_degree::Int=10, seed::Int=42)
    rng = Random.MersenneTwister(seed)

    println("\n" * "="^50)
    println("DETAILED ANALYSIS: n=$n, d=$d")
    println("="^50)

    # Sample points
    println("\n[1] Sampling $n points from unit ball in R^$d...")
    points = sample_unit_ball(n, d; rng=rng)

    # Check radial distribution
    radii = sqrt.(sum(points.^2, dims=2))[:]
    println("    Mean radius: $(round(mean(radii), digits=4))")
    println("    Expected mean for uniform ball: $(round(d/(d+1), digits=4))")

    # Build graph
    println("\n[2] Building geometric graph (target degree ≈ $target_degree)...")
    A, ε, mean_deg = build_geometric_graph(points; target_degree=target_degree)
    num_edges = div(nnz(A), 2)
    println("    ε = $(round(ε, digits=4))")
    println("    Edges: $num_edges")
    println("    Mean degree: $(round(mean_deg, digits=2))")

    # Connectivity
    is_connected, largest_cc = graph_connectivity(A)
    println("    Connected: $is_connected (largest CC: $largest_cc / $n)")

    # Distance statistics
    dists = pairwise_distances(points)
    upper_dists = [dists[i,j] for i in 1:n for j in (i+1):n]
    println("\n    Distance statistics:")
    println("    Mean pairwise distance: $(round(mean(upper_dists), digits=4))")
    println("    √(E[D²]) (Jensen upper bound on E[D]): √(2d/(d+2)) = $(round(sqrt(2*d/(d+2)), digits=4))")

    # Laplacian and eigenvalues
    println("\n[3] Computing normalized Laplacian...")
    L = normalized_laplacian(A)

    println("\n[4] Computing eigenvalues...")
    eigenvalues = compute_eigenvalues(L)
    println("    λ_min = $(round(eigenvalues[1], digits=6)) (should be ≈ 0)")
    println("    λ_2 = $(round(eigenvalues[2], digits=6)) (spectral gap)")
    println("    λ_max = $(round(eigenvalues[end], digits=4))")

    # Heat trace
    println("\n[5] Computing heat trace P(t)...")
    t_values = exp.(range(log(0.1), log(1000.0), length=50))
    P_values = heat_trace_curve(eigenvalues, t_values)

    println("    P(0.1) = $(round(P_values[1], digits=6))")
    println("    P(1.0) = $(round(P_values[10], digits=6))")
    println("    P(10) = $(round(P_values[20], digits=6))")
    println("    P(100) = $(round(P_values[35], digits=6))")

    # Spectral dimension
    println("\n[6] Extracting spectral dimension...")
    t_mid, D_S_running = spectral_dimension_running(t_values, P_values)
    D_S_asymptotic = spectral_dimension_asymptotic(t_values, P_values)

    println("    D_S(t=1) ≈ $(round(D_S_running[10], digits=3))")
    println("    D_S(t=10) ≈ $(round(D_S_running[20], digits=3))")
    println("    D_S(t=100) ≈ $(round(D_S_running[35], digits=3))")
    println("    D_S (asymptotic) = $(round(D_S_asymptotic, digits=3))")

    println("\n" * "="^50)

    return (
        points = points,
        A = A,
        L = L,
        eigenvalues = eigenvalues,
        t_values = t_values,
        P_values = P_values,
        t_mid = t_mid,
        D_S_running = D_S_running,
        D_S_asymptotic = D_S_asymptotic
    )
end

#=============================================================================
  Main Entry Point
=============================================================================#

function main()
    println("Spectral Dimension of Random Geometric Graphs")
    println("Testing the Curse of Dimensionality → D_S(1) = 2 Hypothesis")
    println()

    # Verification on known geometries
    println("="^50)
    println("VERIFICATION ON KNOWN GEOMETRIES")
    println("="^50)
    verify_on_lattice(20, 1)  # Path graph, D_S ≈ 1
    verify_on_lattice(15, 2)  # 2D grid, D_S ≈ 2

    # Detailed analysis for a few cases
    detailed_analysis(500, 3)
    detailed_analysis(500, 30)
    detailed_analysis(500, 100)

    # Full experiment
    println("\n" * "="^50)
    println("RUNNING FULL EXPERIMENT")
    println("="^50)

    results = run_experiment(
        dimensions = [3, 10, 30, 100, 300],
        sample_sizes = [200, 500, 1000],
        num_trials = 3,
        target_degree = 15,
        seed = 42
    )

    print_results(results)
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
