# Random realisable matroids (Project IV)
# The current version works only over Q.

using Random

const QQ = Rational{BigInt}
q(x::Integer) = BigInt(x) // BigInt(1)


# Basic exact linear algebra. These routines work with rational matrices.
function exact_rank(A::AbstractMatrix{QQ})
    R = Matrix(A)
    m, n = size(R)
    row = 1

    for col in 1:n
        row > m && break
        pivot = 0
        for i in row:m
            if !iszero(R[i, col])
                pivot = i
                break
            end
        end
        pivot == 0 && continue
        if pivot != row
            R[row, :], R[pivot, :] = copy(R[pivot, :]), copy(R[row, :])
        end
        for i in (row + 1):m
            if !iszero(R[i, col])
                t = R[i, col] / R[row, col]
                R[i, col] = zero(QQ)
                for j in (col + 1):n
                    R[i, j] -= t * R[row, j]
                end
            end
        end
        row += 1
    end
    return row - 1
end

function exact_det(A::AbstractMatrix{QQ})
    n, m = size(A)
    n == m || error("Determinant requires a square matrix")
    R = Matrix(A)
    ans = one(QQ)

    for col in 1:n
        pivot = 0
        for i in col:n
            if !iszero(R[i, col])
                pivot = i
                break
            end
        end
        pivot == 0 && return zero(QQ)
        if pivot != col
            R[col, :], R[pivot, :] = copy(R[pivot, :]), copy(R[col, :])
            ans = -ans
        end
        a = R[col, col]
        ans *= a
        for i in (col + 1):n
            if !iszero(R[i, col])
                t = R[i, col] / a
                R[i, col] = zero(QQ)
                for j in (col + 1):n
                    R[i, j] -= t * R[col, j]
                end
            end
        end
    end
    return ans
end

# Choose k distinct indices, and choose from a list of positive weights.
choose(rng, xs, k) = sort!(collect(xs)[randperm(rng, length(xs))[1:k]])

function choose_weighted(rng, weights)
    all(w -> w >= 0, weights) || error("Weights must be nonnegative")
    total = sum(weights)
    total > 0 || error("Weights cannot all be zero")
    x = rand(rng) * total
    for i in eachindex(weights)
        x -= weights[i]
        x < 0 && return i
    end
    return length(weights)
end

# A distribution that assigns positive probability to every integer.
function unbounded_integer(rng)
    bits = 1
    while rand(rng, Bool)
        bits += 1
    end
    x = BigInt(0)
    for _ in 1:bits
        x = 2 * x + Int(rand(rng, Bool))
    end
    return rand(rng, Bool) ? x : -x
end

function random_matrix(k::Int, n::Int;
                       rng=Random.default_rng(), mode=:wide,
                       bound=1000, max_tries=1000)
    1 <= k <= n || error("Require 1 <= k <= n")
    bound >= 1 || error("bound must be positive")
    mode in (:wide, :small, :unbounded) || error("Unknown starting distribution")

    for _ in 1:max_tries
        A = Matrix{QQ}(undef, k, n)
        for j in 1:n, i in 1:k
            z = if mode == :wide
                rand(rng, 0:bound)
            elseif mode == :small
                rand(rng, -1:1)
            else
                unbounded_integer(rng)
            end
            A[i, j] = q(z)
        end
        exact_rank(A) == k && return A
    end
    error("Could not generate a rank-$k matrix")
end


# Operation 1: change one entry so that one chosen maximal minor vanishes.
function zero_one_minor!(A::Matrix{QQ}, rng; tries=25)
    k, n = size(A)
    for _ in 1:tries
        B = choose(rng, 1:n, k)
        d = exact_det(A[:, B])
        iszero(d) && continue

        for t in randperm(rng, k), i in randperm(rng, k)
            rows = [r for r in 1:k if r != i]
            cols = [B[s] for s in 1:k if s != t]
            c = (-1)^(i + t) * exact_det(A[rows, cols])
            iszero(c) && continue

            j = B[t]
            old = A[i, j]
            A[i, j] = old - d / c
            exact_rank(A) == k && return true
            A[i, j] = old
        end
    end
    return false
end

# Operation 2: make an independent set into a circuit, possibly a loop.
function impose_circuit!(A::Matrix{QQ}, rng; tries=25)
    k, n = size(A)
    for _ in 1:tries
        r = rand(rng, 1:k)
        S = choose(rng, 1:n, r)
        exact_rank(A[:, S]) == r || continue   # It must be a new dependency.

        target = rand(rng, S)
        sources = [j for j in S if j != target]
        newcol = zeros(QQ, k)
        for j in sources
            coeff = rand(rng, (-3, -2, -1, 1, 2, 3))
            newcol += q(coeff) * A[:, j]
        end

        oldcol = copy(A[:, target])
        A[:, target] = newcol
        exact_rank(A) == k && return true
        A[:, target] = oldcol
    end
    return false
end

# Solve C*u=b over Q. Random small values are used for free variables.
# Return nothing if the equations are inconsistent.
function random_affine_solution(C::Matrix{QQ}, b::Vector{QQ}, rng)
    m, n = size(C)
    R = hcat(C, b)
    pivots = Int[]
    row = 1

    for col in 1:n
        row > m && break
        pivot = 0
        for i in row:m
            if !iszero(R[i, col])
                pivot = i
                break
            end
        end
        pivot == 0 && continue
        if pivot != row
            R[row, :], R[pivot, :] = copy(R[pivot, :]), copy(R[row, :])
        end
        R[row, :] ./= R[row, col]
        for i in 1:m
            i == row && continue
            if !iszero(R[i, col])
                R[i, :] -= R[i, col] * R[row, :]
            end
        end
        push!(pivots, col)
        row += 1
    end

    for i in row:m
        !iszero(R[i, n + 1]) && return nothing
    end

    u = zeros(QQ, n)
    free = [j for j in 1:n if !(j in pivots)]
    for j in free
        u[j] = q(rand(rng, -3:3))
    end
    for (i, j) in enumerate(pivots)
        u[j] = R[i, n + 1] - sum((R[i, h] * u[h] for h in free); init=zero(QQ))
    end
    return u
end

# Operation 3: modify one column to zero several selected maximal minors.
function zero_several_minors!(A::Matrix{QQ}, rng; tries=25)
    k, n = size(A)
    (k >= 3 && n > k) || return false

    for _ in 1:tries
        j = rand(rng, 1:n)
        others = [s for s in 1:n if s != j]
        m = rand(rng, 2:min(k - 1, 4))
        Bs = Vector{Vector{Int}}()

        # Pick distinct nonzero minors containing column j.
        for _ in 1:60
            B = sort!([j; choose(rng, others, k - 1)])
            if !(B in Bs) && !iszero(exact_det(A[:, B]))
                push!(Bs, B)
                length(Bs) == m && break
            end
        end
        length(Bs) == m || continue

        C = Matrix{QQ}(undef, m, k)
        d = Vector{QQ}(undef, m)
        for (ell, B) in enumerate(Bs)
            d[ell] = -exact_det(A[:, B])
            t = findfirst(==(j), B)
            cols = [s for s in B if s != j]
            for i in 1:k
                rows = [s for s in 1:k if s != i]
                C[ell, i] = (-1)^(i + t) * exact_det(A[rows, cols])
            end
        end

        u = random_affine_solution(C, d, rng)
        u === nothing && continue
        oldcol = copy(A[:, j])
        A[:, j] = oldcol + u
        if exact_rank(A) == k && all(B -> iszero(exact_det(A[:, B])), Bs)
            return true
        end
        A[:, j] = oldcol
    end
    return false
end


# Combine the three operations into one sampler.
function sample_matroid(k::Int, n::Int;
                        rng=Random.default_rng(), bound=1000,
                        p_stop=0.30, max_steps=12,
                        start_weights=(0.90, 0.08, 0.02),
                        step_weights=(0.45, 0.35, 0.20),
                        return_details=false)
    0 < p_stop <= 1 || error("Require 0 < p_stop <= 1")
    max_steps >= 0 || error("max_steps must be nonnegative")

    modes = (:wide, :small, :unbounded)
    mode = modes[choose_weighted(rng, start_weights)]
    A = random_matrix(k, n; rng=rng, mode=mode, bound=bound)
    operations = Symbol[]

    while n > k && length(operations) < max_steps
        rand(rng) < p_stop && break

        success = false
        for _ in 1:20
            operation = choose_weighted(rng, step_weights)
            worked = if operation == 1
                zero_one_minor!(A, rng)
            elseif operation == 2
                impose_circuit!(A, rng)
            else
                zero_several_minors!(A, rng)
            end
            if worked
                push!(operations, (:single, :circuit, :multi)[operation])
                success = true
                break
            end
        end
        success || break
    end

    if return_details
        return (matrix=A, start_mode=mode,
                operations=operations, steps=length(operations))
    end
    return A
end


# For small examples, list all k-subsets that are not bases.
function nonbases(A::Matrix{QQ})
    k, n = size(A)
    result = Vector{Vector{Int}}()
    chosen = Int[]

    function visit(first, remaining)
        if remaining == 0
            iszero(exact_det(A[:, chosen])) && push!(result, copy(chosen))
            return
        end
        for j in first:(n - remaining + 1)
            push!(chosen, j)
            visit(j + 1, remaining - 1)
            pop!(chosen)
        end
    end
    visit(1, k)
    return result
end

# Basic checks (not a comprehensive correctness test).
function smoke_test()
    rng = MersenneTwister(1234)
    A = random_matrix(3, 6; rng=rng)
    @assert exact_rank(A) == 3
    for operation in (zero_one_minor!, impose_circuit!, zero_several_minors!)
        B = copy(A)
        @assert operation(B, rng)
        @assert exact_rank(B) == 3
        @assert !isempty(nonbases(B))
    end
    result = sample_matroid(3, 6; rng=rng, return_details=true)
    @assert exact_rank(result.matrix) == 3
    @assert result.steps <= 12
    println("Basic checks passed")
end

# Example usage at the Julia prompt:
# include("random_matroid_sample.jl")
# smoke_test()
# result = sample_matroid(5, 10; return_details=true)
# result.matrix
# nonbases(result.matrix)
