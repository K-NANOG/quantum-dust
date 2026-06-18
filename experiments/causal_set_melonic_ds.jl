#!/usr/bin/env julia
#=
Causal Set & Melonic Tensor Model Spectral Dimension

Phase 147-01: Compute D_S for (a) sprinkled causal sets in M^{1+1} and
(b) melonic tensor model graphs (rank-3 Gurau colored tensors).

The separation theorem predicts:
  - Causal sets (good continuum limits) → spectrally faithful, D_S ~ 1.5–1.7
  - Melonic tensor models (tree-like) → NOT faithful, D_S ~ 1.0–1.3

This is the decisive selectivity test: CDT D_S >> melonic D_S.

Algorithm:
  1. Sprinkle N points in causal diamond in M^{1+1}, compute link graph
  2. Generate melonic graphs via iterative 2-point insertions on colored tensors
  3. Compute D_S(1) via normalized Laplacian eigenvalues
  4. Compare against D_S(K_N, 1) baseline and CDT data from Phase 146

Generates: experiments/data/causal_set_ds.csv, experiments/data/melonic_tensor_ds.csv
=#

using LinearAlgebra
using SparseArrays
using Statistics
using Random
using Printf
using DelimitedFiles

const DATA_DIR = joinpath(@__DIR__, "data")

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
#  Causal set sprinkling in M^{1+1}
# ═══════════════════════════════════════════════════════════════════════════════

"""
    sprinkle_causal_set(N, dim=2; seed=42)

Sprinkle N points uniformly in the causal diamond {(t,x) : |t| + |x| ≤ 1}
in M^{1+1}. Compute the link graph (transitive reduction of the causal order).

Returns (points, A_links) where:
  - points: N×2 matrix of (t, x) coordinates
  - A_links: sparse symmetric adjacency matrix of the largest connected component
"""
function sprinkle_causal_set(N::Int; seed::Int=42)
    rng = Random.MersenneTwister(seed)

    # Rejection sampling in causal diamond {(t,x) : |t| + |x| ≤ 1}
    points = zeros(Float64, N, 2)
    count = 0
    while count < N
        t = 2.0 * rand(rng) - 1.0
        x = 2.0 * rand(rng) - 1.0
        if abs(t) + abs(x) <= 1.0
            count += 1
            points[count, 1] = t
            points[count, 2] = x
        end
    end

    # Sort by time coordinate for efficient causal order computation
    perm = sortperm(points[:, 1])
    points = points[perm, :]

    # Causal order matrix: causal[i,j] = true if i ≺ j (i causally precedes j)
    # i ≺ j iff t_j - t_i > 0 AND (t_j - t_i)² - (x_j - x_i)² > 0
    causal = falses(N, N)
    for i in 1:N
        ti, xi = points[i, 1], points[i, 2]
        for j in (i+1):N
            tj, xj = points[j, 1], points[j, 2]
            dt = tj - ti
            dx = xj - xi
            if dt > 0 && dt^2 - dx^2 > 0
                causal[i, j] = true
            end
        end
    end

    # Link computation: (i,j) is a link if i ≺ j with no intermediate k
    # such that i ≺ k ≺ j
    I_idx = Int[]
    J_idx = Int[]
    for i in 1:N
        for j in (i+1):N
            if !causal[i, j]
                continue
            end
            # Check for intermediate elements
            has_intermediate = false
            for k in (i+1):(j-1)
                if causal[i, k] && causal[k, j]
                    has_intermediate = true
                    break
                end
            end
            if !has_intermediate
                push!(I_idx, i); push!(J_idx, j)
                push!(I_idx, j); push!(J_idx, i)  # undirected
            end
        end
    end

    if isempty(I_idx)
        # Degenerate case: return single-vertex graph
        return points, sparse([1], [1], [0.0], 1, 1)
    end

    # Build sparse adjacency matrix
    A = sparse(I_idx, J_idx, ones(Float64, length(I_idx)), N, N)
    A = min.(A, 1.0)  # clamp duplicates

    # Extract largest connected component
    A_comp, comp_size = largest_connected_component(A)

    return points, A_comp
end

"""
    largest_connected_component(A)

Extract the largest connected component from adjacency matrix A.
Returns (A_sub, size) where A_sub is the submatrix of the largest component.
"""
function largest_connected_component(A)
    N = size(A, 1)
    visited = zeros(Int, N)  # component label for each vertex
    component_id = 0

    for start in 1:N
        if visited[start] != 0
            continue
        end
        component_id += 1
        queue = [start]
        visited[start] = component_id
        while !isempty(queue)
            v = popfirst!(queue)
            for u in 1:N
                if A[v, u] > 0 && visited[u] == 0
                    visited[u] = component_id
                    push!(queue, u)
                end
            end
        end
    end

    # Find largest component
    component_sizes = zeros(Int, component_id)
    for i in 1:N
        component_sizes[visited[i]] += 1
    end
    best_comp = argmax(component_sizes)
    comp_vertices = findall(v -> visited[v] == best_comp, 1:N)

    # Extract submatrix
    A_sub = A[comp_vertices, comp_vertices]
    return A_sub, length(comp_vertices)
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Melonic tensor model graph generation
# ═══════════════════════════════════════════════════════════════════════════════

"""
    generate_melonic_graph(n_insertions, D=3; seed=42)

Generate a melonic tensor model graph via iterative 2-point insertions
on a rank-D colored tensor model.

- Start with initial melon: 2 vertices, D colored edges
- Each insertion: pick random color c, random edge (u,v) of color c,
  delete it, add vertices a,b, add edges (u,a,c), (b,v,c), (a,b,c') for c'≠c
- After n_insertions: N = 2(n_insertions + 1) vertices

Returns sparse symmetric binary adjacency matrix (multi-edges collapsed).
"""
function generate_melonic_graph(n_insertions::Int, D::Int=3; seed::Int=42)
    rng = Random.MersenneTwister(seed)

    # Edge list: Vector of (u, v, color)
    # Initial melon: vertices 1,2 connected by D colored edges
    edges = Tuple{Int,Int,Int}[]
    for c in 0:(D-1)
        push!(edges, (1, 2, c))
    end
    next_vertex = 3

    for _ in 1:n_insertions
        # Pick random color
        c = rand(rng, 0:(D-1))

        # Find all edges of color c
        color_edges = findall(e -> edges[e][3] == c, 1:length(edges))
        if isempty(color_edges)
            continue
        end

        # Pick random edge of color c
        idx = color_edges[rand(rng, 1:length(color_edges))]
        u, v, _ = edges[idx]

        # Delete this edge
        deleteat!(edges, idx)

        # Add new vertices a, b
        a = next_vertex
        b = next_vertex + 1
        next_vertex += 2

        # Add edges: (u, a, c), (b, v, c)
        push!(edges, (u, a, c))
        push!(edges, (b, v, c))

        # Add edges: (a, b, c') for all c' ≠ c
        for cp in 0:(D-1)
            if cp != c
                push!(edges, (a, b, cp))
            end
        end
    end

    # Build binary adjacency matrix
    N = next_vertex - 1  # = 2(n_insertions + 1)
    I_idx = Int[]
    J_idx = Int[]
    for (u, v, _) in edges
        push!(I_idx, u); push!(J_idx, v)
        push!(I_idx, v); push!(J_idx, u)
    end

    A = sparse(I_idx, J_idx, ones(Float64, length(I_idx)), N, N)
    A = min.(A, 1.0)  # collapse multi-edges
    # Zero diagonal
    for i in 1:N
        A[i, i] = 0.0
    end

    return A
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Normalized Laplacian + D_S(1) — shared
# ═══════════════════════════════════════════════════════════════════════════════

"""
    graph_ds_at_t1(A)

Compute D_S(1) from adjacency matrix A via normalized Laplacian.

- Normalized Laplacian: L = I - D^{-1/2}AD^{-1/2}
- D_S(1) = 2·Σ λ_i·e^{-λ_i} / Σ e^{-λ_i}
- Spectral gap = λ_1 (smallest nonzero eigenvalue)
- Laplacian error = max|λ_i(L_G) - λ_i(L_{K_N})|

Returns (ds_t1, spectral_gap, laplacian_error).
"""
function graph_ds_at_t1(A)
    N = size(A, 1)

    # Dense matrix for eigendecomposition
    A_dense = Matrix{Float64}(A)

    # Degrees
    degrees = vec(sum(A_dense, dims=2))
    # Guard against zero-degree vertices
    degrees[degrees .== 0] .= 1.0

    # D^{-1/2}
    D_inv_sqrt = Diagonal(1.0 ./ sqrt.(degrees))

    # Normalized Laplacian: L = I - D^{-1/2} A D^{-1/2}
    L = Matrix{Float64}(I, N, N) - D_inv_sqrt * A_dense * D_inv_sqrt

    # Eigenvalues only
    eigenvalues = eigvals(Symmetric(L))
    eigenvalues = max.(eigenvalues, 0.0)
    sort!(eigenvalues)

    # Spectral gap: smallest nonzero eigenvalue
    spectral_gap = length(eigenvalues) >= 2 ? eigenvalues[2] : 0.0

    # D_S(1) = 2·Σ λ_i·e^{-λ_i} / Σ e^{-λ_i}
    exp_neg_lam = exp.(-eigenvalues)
    numerator = sum(eigenvalues .* exp_neg_lam)
    denominator = sum(exp_neg_lam)
    ds_t1 = denominator > 0 ? 2.0 * numerator / denominator : NaN

    # Laplacian error: eigenvalue comparison with K_N
    kn_eigenvalues = vcat([0.0], fill(N / (N - 1), N - 1))
    diff_eigenvalues = sort(eigenvalues) .- sort(kn_eigenvalues)
    laplacian_error = maximum(abs.(diff_eigenvalues))

    return (ds_t1, spectral_gap, laplacian_error)
end

# ─── Configuration ───────────────────────────────────────────────────────────

const CS_SIZES = [64, 100, 144, 256, 400]
const CS_N_TRIALS = 5
const CS_SEED = 42

const MELONIC_CONFIGS = [
    (n_ins=31,  D=3),   # N=64
    (n_ins=49,  D=3),   # N=100
    (n_ins=71,  D=3),   # N=144
    (n_ins=127, D=3),   # N=256
    (n_ins=199, D=3),   # N=400
]
const MELONIC_N_TRIALS = 5
const MELONIC_SEED = 42

# ═══════════════════════════════════════════════════════════════════════════════
#  Benchmark experiments
# ═══════════════════════════════════════════════════════════════════════════════

function run_causal_set_experiment()
    RowType = NamedTuple{(:N,:N_component,:trial,:ds_t1,:ds_km,:ds_gap,:spectral_gap,:mean_degree,:n_links),
                         Tuple{Int,Int,Int,Float64,Float64,Float64,Float64,Float64,Int}}
    rows = RowType[]

    total = length(CS_SIZES) * CS_N_TRIALS
    progress = 0

    for N in CS_SIZES
        ds_km = ds_km_analytical(N)

        for trial in 1:CS_N_TRIALS
            progress += 1
            seed = CS_SEED + trial - 1

            @printf("  [%d/%d] Causal set N=%d, trial=%d: ", progress, total, N, trial)

            pts, A_cs = sprinkle_causal_set(N; seed=seed)
            N_comp = size(A_cs, 1)
            n_links = div(nnz(A_cs), 2)
            mean_deg = N_comp > 0 ? mean(vec(sum(A_cs, dims=2))) : 0.0

            ds_t1, spectral_gap, _ = graph_ds_at_t1(A_cs)
            ds_km_comp = ds_km_analytical(N_comp)
            ds_gap = abs(ds_t1 - ds_km_comp)

            @printf("N_comp=%d, D_S=%.4f (K_%d=%.4f), gap=%.4f, deg=%.1f, links=%d\n",
                    N_comp, ds_t1, N_comp, ds_km_comp, ds_gap, mean_deg, n_links)

            push!(rows, (
                N=N, N_component=N_comp, trial=trial,
                ds_t1=ds_t1, ds_km=ds_km_comp, ds_gap=ds_gap,
                spectral_gap=spectral_gap, mean_degree=mean_deg, n_links=n_links
            ))
        end
    end

    return rows
end

function run_melonic_experiment()
    RowType = NamedTuple{(:n_insertions,:D,:N,:trial,:ds_t1,:ds_km,:ds_gap,:spectral_gap,:mean_degree),
                         Tuple{Int,Int,Int,Int,Float64,Float64,Float64,Float64,Float64}}
    rows = RowType[]

    total = length(MELONIC_CONFIGS) * MELONIC_N_TRIALS
    progress = 0

    for cfg in MELONIC_CONFIGS
        n_ins, D = cfg.n_ins, cfg.D
        N = 2 * (n_ins + 1)
        ds_km = ds_km_analytical(N)

        for trial in 1:MELONIC_N_TRIALS
            progress += 1
            seed = MELONIC_SEED + trial - 1

            @printf("  [%d/%d] Melonic n_ins=%d, D=%d (N=%d), trial=%d: ", progress, total, n_ins, D, N, trial)

            A_m = generate_melonic_graph(n_ins, D; seed=seed)
            mean_deg = mean(vec(sum(A_m, dims=2)))

            ds_t1, spectral_gap, _ = graph_ds_at_t1(A_m)
            ds_gap = abs(ds_t1 - ds_km)

            @printf("D_S=%.4f (K_%d=%.4f), gap=%.4f, deg=%.1f\n",
                    ds_t1, N, ds_km, ds_gap, mean_deg)

            push!(rows, (
                n_insertions=n_ins, D=D, N=N, trial=trial,
                ds_t1=ds_t1, ds_km=ds_km, ds_gap=ds_gap,
                spectral_gap=spectral_gap, mean_degree=mean_deg
            ))
        end
    end

    return rows
end

# ═══════════════════════════════════════════════════════════════════════════════
#  CSV output
# ═══════════════════════════════════════════════════════════════════════════════

function write_causal_set_csv(rows)
    mkpath(DATA_DIR)
    path = joinpath(DATA_DIR, "causal_set_ds.csv")
    open(path, "w") do io
        println(io, "N,N_component,trial,ds_t1,ds_km,ds_gap,spectral_gap,mean_degree,n_links")
        for r in rows
            @printf(io, "%d,%d,%d,%.8e,%.8e,%.8e,%.8e,%.8e,%d\n",
                    r.N, r.N_component, r.trial, r.ds_t1, r.ds_km, r.ds_gap,
                    r.spectral_gap, r.mean_degree, r.n_links)
        end
    end
    println("  Wrote $path  ($(length(rows)) rows)")
end

function write_melonic_csv(rows)
    mkpath(DATA_DIR)
    path = joinpath(DATA_DIR, "melonic_tensor_ds.csv")
    open(path, "w") do io
        println(io, "n_insertions,D,N,trial,ds_t1,ds_km,ds_gap,spectral_gap,mean_degree")
        for r in rows
            @printf(io, "%d,%d,%d,%d,%.8e,%.8e,%.8e,%.8e,%.8e\n",
                    r.n_insertions, r.D, r.N, r.trial, r.ds_t1, r.ds_km, r.ds_gap,
                    r.spectral_gap, r.mean_degree)
        end
    end
    println("  Wrote $path  ($(length(rows)) rows)")
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Comparative summary
# ═══════════════════════════════════════════════════════════════════════════════

function print_comparative_summary(cs_rows, mel_rows)
    println("\n── Separation Theorem Selectivity: CDT vs Causal Set vs Melonic ──")
    println()

    # Try to load CDT data
    cdt_path = joinpath(DATA_DIR, "cdt_spectral_dimension.csv")
    cdt_ds_by_N = Dict{Int, Float64}()
    if isfile(cdt_path)
        lines = readlines(cdt_path)
        for line in lines[2:end]
            vals = split(line, ",")
            N = parse(Int, vals[3])
            ds = parse(Float64, vals[5])
            cdt_ds_by_N[N] = get(cdt_ds_by_N, N, 0.0) == 0.0 ? ds : (cdt_ds_by_N[N] + ds) / 2
        end
        # Recompute proper means
        cdt_ds_by_N = Dict{Int, Float64}()
        cdt_counts = Dict{Int, Int}()
        for line in lines[2:end]
            vals = split(line, ",")
            N = parse(Int, vals[3])
            ds = parse(Float64, vals[5])
            cdt_ds_by_N[N] = get(cdt_ds_by_N, N, 0.0) + ds
            cdt_counts[N] = get(cdt_counts, N, 0) + 1
        end
        for N in keys(cdt_ds_by_N)
            cdt_ds_by_N[N] /= cdt_counts[N]
        end
    end

    @printf("  %-6s  %-10s  %-10s  %-10s  %-14s\n",
            "N", "CDT", "Causal", "Melonic", "CDT-Mel gap")
    println("  ", "-" ^ 56)

    for N in CS_SIZES
        cs_matching = filter(r -> r.N == N, cs_rows)
        mel_matching = filter(r -> r.N == N, mel_rows)

        cs_ds = isempty(cs_matching) ? NaN : mean([r.ds_t1 for r in cs_matching])
        mel_ds = isempty(mel_matching) ? NaN : mean([r.ds_t1 for r in mel_matching])
        cdt_ds = get(cdt_ds_by_N, N, NaN)

        gap = isnan(cdt_ds) || isnan(mel_ds) ? NaN : cdt_ds - mel_ds

        cdt_str = isnan(cdt_ds) ? "—" : @sprintf("%.4f", cdt_ds)
        cs_str = isnan(cs_ds) ? "—" : @sprintf("%.4f", cs_ds)
        mel_str = isnan(mel_ds) ? "—" : @sprintf("%.4f", mel_ds)
        gap_str = isnan(gap) ? "—" : @sprintf("%.4f", gap)

        @printf("  %-6d  %-10s  %-10s  %-10s  %-14s\n", N, cdt_str, cs_str, mel_str, gap_str)
    end

    # Overall means
    cs_mean = mean([r.ds_t1 for r in cs_rows])
    mel_mean = mean([r.ds_t1 for r in mel_rows])
    println()
    @printf("  Overall mean D_S(1):  Causal=%.4f  Melonic=%.4f  Separation=%.4f\n",
            cs_mean, mel_mean, cs_mean - mel_mean)

    if !isempty(cdt_ds_by_N)
        cdt_mean = mean(values(cdt_ds_by_N))
        @printf("  CDT mean D_S(1)=%.4f  CDT-Melonic gap=%.4f\n", cdt_mean, cdt_mean - mel_mean)
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════════════════════

function main()
    println("=" ^ 70)
    println("CAUSAL SET & MELONIC TENSOR MODEL: SEPARATION THEOREM SELECTIVITY")
    println("=" ^ 70)
    println()

    println("── Causal Set Experiment ──")
    println("  sizes = $CS_SIZES, trials = $CS_N_TRIALS, seed = $CS_SEED")
    println()
    cs_rows = run_causal_set_experiment()

    println("\n── Writing Causal Set CSV ──")
    write_causal_set_csv(cs_rows)

    println("\n── Melonic Tensor Model Experiment ──")
    println("  configs = $MELONIC_CONFIGS, trials = $MELONIC_N_TRIALS, seed = $MELONIC_SEED")
    println()
    mel_rows = run_melonic_experiment()

    println("\n── Writing Melonic CSV ──")
    write_melonic_csv(mel_rows)

    print_comparative_summary(cs_rows, mel_rows)

    println()
    println("=" ^ 70)
    println("COMPLETE: Separation theorem selectivity test finished.")
    println("=" ^ 70)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
