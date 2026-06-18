#!/usr/bin/env julia
#=
Tensor Network CV²: MPS and MERA States on CP^n

Phase 52-01: Test whether the concentration mechanism (CV² → 0) survives
beyond Haar measure by computing CV² for random MPS and random MERA states,
comparing against Haar-random baselines at the same Hilbert space dimension.

Key question: Is the Haar assumption (Tier 2 indecomposability) necessary
for the qualitative conclusion DS → 2, or do structured tensor network
states also concentrate?

MPS: Random matrix product states with bond dimension chi on L sites
     with local dimension d. State lives on CP^{d^L - 1}.

MERA: Simplified binary MERA with random disentanglers (Haar on U(d²))
      and random isometries (via QR on Gaussian matrices). State lives
      on CP^{d^L - 1}.

Generates: experiments/data/tensor_network_cv2.csv
=#

include(joinpath(@__DIR__, "spectral_dimension.jl"))

using Printf

# ─── Configuration ───────────────────────────────────────────────────────────
const M_STATES  = 200     # number of states to sample per trial
const N_TRIALS  = 5       # for error bars
const SEED      = 42

# MPS configurations: (L, d, chi) → n+1 = d^L
const MPS_CONFIGS = [
    (4,  2, 2),    # n+1 = 16
    (5,  2, 4),    # n+1 = 32
    (6,  2, 8),    # n+1 = 64
    (8,  2, 4),    # n+1 = 256
    (10, 2, 2),    # n+1 = 1024
]

# MERA configurations: (L, d) → n+1 = d^L, chi = d² by construction
const MERA_CONFIGS = [
    (8,  2),       # n+1 = 256
    (16, 2),       # n+1 = 65536
]

# ─── Output directory ────────────────────────────────────────────────────────
const DATA_DIR = joinpath(@__DIR__, "data")
mkpath(DATA_DIR)

# ═══════════════════════════════════════════════════════════════════════════════
#  Sampling functions (reuse fubini_study_distance pattern from cpn_concentration.jl)
# ═══════════════════════════════════════════════════════════════════════════════

"""
    sample_haar_states(n_plus_1, m, rng)

Sample `m` Haar-random quantum states on CP^{n_plus_1 - 1}.
Returns an m × n_plus_1 complex matrix where each row is a normalized state.
"""
function sample_haar_states(n_plus_1::Int, m::Int, rng)
    Z = randn(rng, ComplexF64, m, n_plus_1)
    for i in 1:m
        Z[i, :] ./= norm(Z[i, :])
    end
    return Z
end

"""
    fubini_study_distance(psi, phi)

Compute the Fubini-Study distance d_FS = arccos(|⟨ψ|ϕ⟩|).
"""
function fubini_study_distance(psi::AbstractVector, phi::AbstractVector)
    overlap = abs(dot(psi, phi))
    return acos(min(1.0, overlap))
end

"""
    compute_cv_squared(states)

Given an m × dim matrix of normalized states, compute all pairwise
Fubini-Study distances and return CV² = Var(d) / Mean(d)².
"""
function compute_cv_squared(states::AbstractMatrix)
    m = size(states, 1)
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
#  MPS state generation
# ═══════════════════════════════════════════════════════════════════════════════

"""
    sample_random_mps(L, d, chi, rng)

Generate a random MPS state on L sites with local dimension d and bond
dimension chi. Returns a normalized state vector in C^{d^L}.

Algorithm: Contract site by site from left using random tensors
A_i of shape (chi, d, chi) with i.i.d. complex Gaussian entries.
Boundary tensors: A_1 is (1, d, chi), A_L is (chi, d, 1).
"""
function sample_random_mps(L::Int, d::Int, chi::Int, rng)
    # Build state by iterated matrix multiplication
    # At each site, we have a (chi_left,) vector that becomes (chi_left * d,)
    # after tensoring with local basis, then contracted to (chi_right,).

    # Start: boundary vector of dimension 1
    # After site 1: vector of dimension chi
    # After site i (1 < i < L): vector of dimension chi
    # After site L: vector of dimension 1 (scalar)

    # We work in the "transfer matrix" picture:
    # state[s1, s2, ..., sL] = A1[s1] * A2[s2] * ... * AL[sL]
    # where Ai[si] is a chi_left × chi_right matrix for each physical index si.

    dim = d^L
    state = zeros(ComplexF64, dim)

    # For each computational basis configuration (s1, ..., sL),
    # compute the MPS amplitude by matrix chain multiplication.
    # This is O(d^L * L * chi^2) which is fine for our small sizes.

    # Pregenerate all MPS tensors
    # A[site][physical_index] = chi_left × chi_right matrix
    tensors = Vector{Vector{Matrix{ComplexF64}}}(undef, L)

    # Site 1: (1, d, chi) → d matrices of size 1 × chi
    tensors[1] = [randn(rng, ComplexF64, 1, chi) for _ in 1:d]

    # Bulk sites: (chi, d, chi) → d matrices of size chi × chi
    for site in 2:(L-1)
        tensors[site] = [randn(rng, ComplexF64, chi, chi) for _ in 1:d]
    end

    # Site L: (chi, d, 1) → d matrices of size chi × 1
    tensors[L] = [randn(rng, ComplexF64, chi, 1) for _ in 1:d]

    # Contract for each basis state
    for idx in 0:(dim-1)
        # Decode index into physical indices (0-based)
        config = Vector{Int}(undef, L)
        tmp = idx
        for site in L:-1:1
            config[site] = (tmp % d) + 1  # 1-based physical index
            tmp = tmp ÷ d
        end

        # Matrix chain: A1[s1] * A2[s2] * ... * AL[sL]
        result = tensors[1][config[1]]  # 1 × chi
        for site in 2:L
            result = result * tensors[site][config[site]]
        end
        # result is 1×1 matrix
        state[idx + 1] = result[1, 1]
    end

    # Normalize
    state ./= norm(state)
    return state
end

"""
    sample_mps_states(L, d, chi, m, rng)

Sample m random MPS states and return as m × d^L matrix.
"""
function sample_mps_states(L::Int, d::Int, chi::Int, m::Int, rng)
    dim = d^L
    states = Matrix{ComplexF64}(undef, m, dim)
    for i in 1:m
        states[i, :] = sample_random_mps(L, d, chi, rng)
    end
    return states
end

# ═══════════════════════════════════════════════════════════════════════════════
#  MERA state generation
# ═══════════════════════════════════════════════════════════════════════════════

"""
    random_haar_unitary(d, rng)

Generate a Haar-random unitary matrix of size d × d via QR decomposition
of a complex Gaussian matrix.
"""
function random_haar_unitary(d::Int, rng)
    Z = randn(rng, ComplexF64, d, d)
    Q, R = qr(Z)
    Q = Matrix(Q)
    # Fix phase to get true Haar distribution
    D = Diagonal(sign.(diag(R)))
    return Q * D
end

"""
    random_isometry(d_in, d_out, rng)

Generate a random isometry from C^{d_in} to C^{d_out} (d_out ≥ d_in)
via QR of a Gaussian matrix. Returns d_out × d_in matrix with orthonormal columns.
"""
function random_isometry(d_in::Int, d_out::Int, rng)
    @assert d_out >= d_in
    Z = randn(rng, ComplexF64, d_out, d_in)
    Q, _ = qr(Z)
    return Matrix(Q)[:, 1:d_in]
end

"""
    sample_random_mera(L, d, rng)

Generate a random binary MERA state on L sites with local dimension d.
Returns a normalized state vector in C^{d^L}.

Simplified binary MERA structure:
- Start with a random top-level state (single site, dimension d)
- At each layer (top to bottom):
  1. Apply isometries: each isometry maps 1 site → 2 sites (d → d²),
     doubling the number of sites
  2. Apply disentanglers: 2-site Haar-random unitaries on adjacent pairs

L must be a power of 2.
"""
function sample_random_mera(L::Int, d::Int, rng)
    @assert ispow2(L) "MERA requires L to be a power of 2"

    n_layers = Int(log2(L))

    # Start with random top-level state on 1 site of dimension d
    state = randn(rng, ComplexF64, d)
    state ./= norm(state)

    current_sites = 1

    for layer in 1:n_layers
        new_sites = current_sites * 2
        new_dim = d^new_sites

        # Step 1: Apply isometries (each site → 2 sites)
        # Each isometry: d → d² (represented as d² × d matrix)
        # The full isometry on all sites: tensor product of per-site isometries
        expanded = ones(ComplexF64, 1)
        # We need to expand the state by applying isometries site by site
        # Current state has dimension d^current_sites
        # We reshape as (d, d, ..., d) with current_sites indices

        # For each site, apply a random isometry d → d²
        # This maps d^current_sites → (d²)^current_sites = d^(2*current_sites)
        isometries = [random_isometry(d, d^2, rng) for _ in 1:current_sites]

        # Apply isometries via tensor product expansion
        # state is a vector of length d^current_sites
        # Reshape to tensor, apply isometry to each index, reshape back
        state_tensor = reshape(state, ntuple(_ -> d, current_sites)...)

        # Build expanded state by applying isometries to each site
        # Result has dimensions (d², d², ..., d²) with current_sites indices
        # = d^(2*current_sites) total dimension
        new_state = zeros(ComplexF64, ntuple(_ -> d^2, current_sites)...)

        # Apply isometries one site at a time
        # This is equivalent to: new_state = (V₁ ⊗ V₂ ⊗ ... ⊗ Vₖ) * state
        # We do it iteratively

        # Start from state as d^current_sites vector
        vec = copy(state)
        for s in 1:current_sites
            # Apply isometry to site s
            # Current shape: (d^(s-1) * d² ^(0... wait, need to track dimensions)
            # Simpler: reshape so site s is the last index, apply, reshape back

            # Dimensions before site s have been expanded to d²
            # Dimensions after site s are still d
            left_dim = (d^2)^(s-1)
            right_dim = d^(current_sites - s)
            mid_dim = d  # current site dimension

            mat = reshape(vec, left_dim * right_dim, mid_dim)
            # Apply isometry: (d² × d) on the mid dimension
            mat = mat * transpose(isometries[s])  # (left*right) × d²
            vec = reshape(mat, left_dim * d^2 * right_dim)

            # Need to reorder: we have (left, right, d²) but want (left, d², right)
            # Actually let me redo this more carefully
        end

        # Simpler approach: direct tensor product of isometries applied to state
        # V_total = V_1 ⊗ V_2 ⊗ ... ⊗ V_k (each d² × d)
        # new_state = V_total * state
        # V_total has size d^(2k) × d^k

        # Build V_total via iterated Kronecker product
        V_total = isometries[1]  # d² × d
        for s in 2:current_sites
            V_total = kron(V_total, isometries[s])
        end
        expanded_state = V_total * state  # d^(2*current_sites) vector

        # Step 2: Apply disentanglers (2-site unitaries on adjacent pairs)
        # Now we have new_sites = 2*current_sites sites, each of dimension d
        # Apply Haar-random unitaries on pairs (1,2), (3,4), ..., (new_sites-1, new_sites)
        n_pairs = new_sites ÷ 2
        for p in 1:n_pairs
            # Disentangler acts on sites (2p-1, 2p), dimension d² × d²
            U = random_haar_unitary(d^2, rng)

            # Apply U to the pair of sites
            # Reshape state: (d^(2p-2), d², d^(new_sites-2p))
            left_dim = d^(2*p - 2)
            right_dim = d^(new_sites - 2*p)
            mid_dim = d^2

            mat = reshape(expanded_state, left_dim, mid_dim, right_dim)
            # Apply U to middle dimension
            for l in 1:left_dim
                for r in 1:right_dim
                    mat[l, :, r] = U * mat[l, :, r]
                end
            end
            expanded_state = reshape(mat, d^new_sites)
        end

        state = expanded_state
        state ./= norm(state)  # renormalize for numerical stability
        current_sites = new_sites
    end

    return state
end

"""
    sample_mera_states(L, d, m, rng)

Sample m random MERA states and return as m × d^L matrix.
"""
function sample_mera_states(L::Int, d::Int, m::Int, rng)
    dim = d^L
    states = Matrix{ComplexF64}(undef, m, dim)
    for i in 1:m
        states[i, :] = sample_random_mera(L, d, rng)
    end
    return states
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main experiment
# ═══════════════════════════════════════════════════════════════════════════════

function run_tensor_network_experiment()
    rng = Random.MersenneTwister(SEED)

    # Collect rows: (state_type, L, d, chi, n_plus_1, trial, cv2, haar_cv2, ratio, bound)
    rows = Tuple{String, Int, Int, Int, Int, Int, Float64, Float64, Float64, Float64}[]

    # ── MPS configurations ──
    println("\n── MPS configurations ──")
    for (L, d, chi) in MPS_CONFIGS
        n_plus_1 = d^L
        bound = 1.0 / n_plus_1
        println("  MPS: L=$L, d=$d, chi=$chi → n+1=$n_plus_1")

        for trial in 1:N_TRIALS
            # Sample MPS states
            mps_states = sample_mps_states(L, d, chi, M_STATES, rng)
            cv2_mps = compute_cv_squared(mps_states)

            # Sample Haar states at same dimension for comparison
            haar_states = sample_haar_states(n_plus_1, M_STATES, rng)
            cv2_haar = compute_cv_squared(haar_states)

            ratio = cv2_mps / cv2_haar
            push!(rows, ("MPS", L, d, chi, n_plus_1, trial, cv2_mps, cv2_haar, ratio, bound))

            @printf("    trial=%d  CV²(MPS)=%.4e  CV²(Haar)=%.4e  ratio=%.4f\n",
                    trial, cv2_mps, cv2_haar, ratio)
        end
    end

    # ── MERA configurations ──
    println("\n── MERA configurations ──")
    for (L, d) in MERA_CONFIGS
        n_plus_1 = d^L
        chi = d^2  # MERA bond dimension by construction
        bound = 1.0 / n_plus_1

        if n_plus_1 > 1024
            println("  MERA: L=$L, d=$d → n+1=$n_plus_1 (SKIPPING: too large for pairwise distances)")
            continue
        end

        println("  MERA: L=$L, d=$d → n+1=$n_plus_1")

        for trial in 1:N_TRIALS
            # Sample MERA states
            mera_states = sample_mera_states(L, d, M_STATES, rng)
            cv2_mera = compute_cv_squared(mera_states)

            # Sample Haar states at same dimension for comparison
            haar_states = sample_haar_states(n_plus_1, M_STATES, rng)
            cv2_haar = compute_cv_squared(haar_states)

            ratio = cv2_mera / cv2_haar
            push!(rows, ("MERA", L, d, chi, n_plus_1, trial, cv2_mera, cv2_haar, ratio, bound))

            @printf("    trial=%d  CV²(MERA)=%.4e  CV²(Haar)=%.4e  ratio=%.4f\n",
                    trial, cv2_mera, cv2_haar, ratio)
        end
    end

    return rows
end

# ═══════════════════════════════════════════════════════════════════════════════
#  CSV writing
# ═══════════════════════════════════════════════════════════════════════════════

function write_csv(rows)
    path = joinpath(DATA_DIR, "tensor_network_cv2.csv")
    open(path, "w") do io
        println(io, "state_type,L,d,chi,n_plus_1,trial,cv_squared,haar_cv_squared,ratio_to_haar,bound_1_over_n_plus_1")
        for (stype, L, d, chi, n1, trial, cv2, hcv2, ratio, bound) in rows
            @printf(io, "%s,%d,%d,%d,%d,%d,%.8e,%.8e,%.8e,%.8e\n",
                    stype, L, d, chi, n1, trial, cv2, hcv2, ratio, bound)
        end
    end
    println("  Wrote $path  ($(length(rows)) rows)")
end

# ═══════════════════════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════════════════════

function main()
    println("=" ^ 70)
    println("TENSOR NETWORK CV²: MPS AND MERA ON CP^n")
    println("=" ^ 70)
    println("  MPS configs: $(MPS_CONFIGS)")
    println("  MERA configs: $(MERA_CONFIGS)")
    println("  m=$M_STATES states, $N_TRIALS trials, seed=$SEED")

    rows = run_tensor_network_experiment()

    println("\n── Writing CSV ──")
    write_csv(rows)

    # ── Summary table ──
    println("\n── Summary: mean CV² across trials ──")
    @printf("  %-6s  %6s  %3s  %3s  %8s  %12s  %12s  %12s  %8s\n",
            "type", "L", "d", "chi", "n+1", "mean_cv2", "mean_haar", "bound", "ratio")
    println("  ", "-" ^ 82)

    # Group by (state_type, L, d, chi, n_plus_1)
    configs_seen = unique([(r[1], r[2], r[3], r[4], r[5]) for r in rows])
    for (stype, L, d, chi, n1) in configs_seen
        subset = filter(r -> r[1] == stype && r[2] == L && r[3] == d && r[4] == chi && r[5] == n1, rows)
        cv2_vals = [r[7] for r in subset]
        haar_vals = [r[8] for r in subset]
        bound = 1.0 / n1
        m_cv2 = mean(cv2_vals)
        m_haar = mean(haar_vals)
        ratio = m_cv2 / m_haar

        @printf("  %-6s  %6d  %3d  %3d  %8d  %12.4e  %12.4e  %12.4e  %8.4f\n",
                stype, L, d, chi, n1, m_cv2, m_haar, bound, ratio)
    end

    # ── Monotonicity check for MPS ──
    println("\n── Monotonicity check (CV² decreases with n+1) ──")
    mps_rows = filter(r -> r[1] == "MPS", rows)
    mps_configs = sort(unique([(r[2], r[3], r[4], r[5]) for r in mps_rows]), by=x->x[4])
    prev_cv2 = Inf
    monotone = true
    for (L, d, chi, n1) in mps_configs
        subset = filter(r -> r[1] == "MPS" && r[5] == n1, mps_rows)
        m_cv2 = mean([r[7] for r in subset])
        if m_cv2 > prev_cv2
            monotone = false
        end
        prev_cv2 = m_cv2
        @printf("  n+1=%4d  mean_CV²=%.4e\n", n1, m_cv2)
    end

    if monotone
        println("  PASS: MPS CV² decreases monotonically with n+1.")
    else
        println("  NOTE: MPS CV² is not strictly monotonically decreasing with n+1.")
        println("        (Expected: bond dimension chi also affects concentration.)")
    end

    println()
    println("=" ^ 70)
    println("COMPLETE: Tensor network CV² experiment finished.")
    println("=" ^ 70)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
