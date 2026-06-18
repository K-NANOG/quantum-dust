#!/usr/bin/env julia
#=
Verification: Complete Graph has D_S(t=1) = 2

Theoretical prediction:
- Complete graph K_n has eigenvalues λ₁=0 (once), λ₂=...=λₙ=n/(n-1) (n-1 times)
- P(t) = (1/n)[1 + (n-1)exp(-t·n/(n-1))]
- For large n: P(t) ≈ exp(-t), giving D_S(t) = 2t. At t=1: D_S(1) = 2
=#

include("spectral_dimension.jl")

using Printf

# MEASUREMENT SCALE: t = 1
# For K_n with normalized Laplacian, the spectral gap is λ₁ = n/(n-1) → 1.
# The mixing time is t_mix ~ 1/λ₁ → 1, so t = 1 probes the graph at its
# characteristic diffusion scale. This is the natural UV scale for the
# normalized Laplacian.
#
# D_S(t) = 2t for K_n in the n→∞ limit, so D_S(1) = 2 is specific to
# this measurement scale. At other scales: D_S(0.5) = 1, D_S(2) = 4, etc.
# See paper §3.3 (rem:ds-scale-dependence) for the physical interpretation.

"""
Build a complete graph on n vertices.
"""
function complete_graph(n::Int)
    A = ones(n, n) - I(n)
    return sparse(A)
end

"""
Theoretical heat trace for complete graph.
"""
function theoretical_heat_trace_complete(n::Int, t::Float64)
    λ = n / (n - 1)
    return (1 + (n-1) * exp(-t * λ)) / n
end

"""
Verify D_S(t=1) = 2 for complete graphs of various sizes.
"""
function verify_complete_graph()
    println("="^70)
    println("COMPLETE GRAPH SPECTRAL DIMENSION VERIFICATION")
    println("="^70)

    println("\nTheory: K_n has λ₁=0, λ₂=...=λₙ = n/(n-1)")
    println("        P(t) = [1 + (n-1)exp(-nt/(n-1))]/n")
    println("        For large n: D_S(t) = 2t, so D_S(1) = 2")
    println("-"^70)

    for n in [50, 100, 200, 500, 1000]
        A = complete_graph(n)
        L = normalized_laplacian(A)
        eigenvalues = compute_eigenvalues(L)

        # Verify eigenvalue structure
        λ_expected = n / (n - 1)
        λ_actual = eigenvalues[2]

        println("\nn = $n:")
        println("  λ₁ = $(round(eigenvalues[1], digits=6)) (expected: 0)")
        println("  λ₂ = $(round(λ_actual, digits=6)) (expected: $(round(λ_expected, digits=6)))")
        println("  λₙ = $(round(eigenvalues[end], digits=6)) (expected: $(round(λ_expected, digits=6)))")

        # Compute D_S at t=1
        t_values = exp.(range(log(0.1), log(100.0), length=50))
        P_values = heat_trace_curve(eigenvalues, t_values)
        t_mid, D_S_running = spectral_dimension_running(t_values, P_values)

        idx_t1 = argmin(abs.(t_mid .- 1.0))
        D_S_at_1 = D_S_running[idx_t1]

        # Theoretical P(t) check
        P_theoretical_1 = theoretical_heat_trace_complete(n, 1.0)
        P_numerical_1 = heat_trace(eigenvalues, 1.0)

        println("  P(t=1) numerical:   $(round(P_numerical_1, digits=6))")
        println("  P(t=1) theoretical: $(round(P_theoretical_1, digits=6))")
        println("  D_S(t=1) = $(round(D_S_at_1, digits=4))")
    end

    # Theoretical analysis
    println("\n" * "="^70)
    println("ANALYTICAL DERIVATION OF D_S(t) = 2t (hence D_S(1) = 2)")
    println("="^70)

    println("""

For the complete graph K_n:

P(t) = (1/n)[1 + (n-1)exp(-t·n/(n-1))]

Let τ = t·n/(n-1). For n → ∞, τ → t.

P(t) = (1/n) + (1 - 1/n)exp(-τ)
     ≈ exp(-τ)  for large n

So: log P(t) ≈ -t

Therefore: d(log P)/d(log t) = d(-t)/d(log t) = -t

And: D_S(t) = -2 × d(log P)/d(log t) = 2t

At t = 1: D_S(1) = 2. Note that D_S(t) = 2t is linear, NOT a plateau.
The value 2 is specific to the mixing time t = 1.

For finite n, the 1/n term creates a floor that prevents P(t) from
decaying below 1/n, which causes D_S to drop at large t.

The key insight: At short times (t small compared to n), the complete
graph exhibits D_S(t) ≈ 2t, giving D_S(1) ≈ 2 regardless of graph size.
    """)

    # Show D_S(t) curve for complete graphs
    println("="^70)
    println("D_S(t) FOR COMPLETE GRAPHS")
    println("="^70)

    println("\n    t    |  n=50   | n=100  | n=500  | n=1000 |")
    println("-"^55)

    for n in [50, 100, 500, 1000]
        A = complete_graph(n)
        L = normalized_laplacian(A)
        eigenvalues = compute_eigenvalues(L)
        t_values = exp.(range(log(0.1), log(50.0), length=40))
        P_values = heat_trace_curve(eigenvalues, t_values)
        t_mid, D_S_running = spectral_dimension_running(t_values, P_values)

        if n == 50
            for (i, t) in enumerate(t_mid[1:5:end])
                D_S_values = [D_S_running[1 + 5*(j-1)] for j in 1:4]
                if i == 1
                    println(" $(lpad(@sprintf("%.2f", t), 6)) |  $(lpad(@sprintf("%.3f", D_S_values[1]), 5))  |")
                end
            end
        end
    end

    # More complete table
    println("\nD_S at t=1 for various n:")
    for n in [50, 100, 200, 500, 1000, 2000]
        A = complete_graph(n)
        L = normalized_laplacian(A)
        eigenvalues = compute_eigenvalues(L)

        t = 1.0
        P_t = heat_trace(eigenvalues, t)
        P_t_eps = heat_trace(eigenvalues, t * 1.01)

        D_S = -2 * (log(P_t_eps) - log(P_t)) / (log(t * 1.01) - log(t))
        println("  n = $(lpad(n, 4)): D_S(t=1) = $(round(D_S, digits=4))")
    end
end

function main_verify()
    verify_complete_graph()

    println("\n" * "="^70)
    println("CONCLUSION: COMPLETE GRAPH HAS D_S(1) → 2 AS n → ∞ (more precisely, D_S(t) = 2t)")
    println("="^70)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main_verify()
end
