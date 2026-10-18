# Benchmarking for the Project IV random matroid sampler.
# Keep the sampling operations in random_matroid_sampler.jl.
# Loading this file also loads the sampler if needed.

using Printf

if !isdefined(@__MODULE__, :sample_matroid)
    include(joinpath(@__DIR__, "random_matroid_sampler.jl"))
end

# Enumerate all k-subsets of [n].
function k_subsets(n::Int, k::Int)
    out = Vector{Vector{Int}}()
    0 <= k <= n || return out
    chosen = Int[]
    function visit(first::Int, remaining::Int)
        if remaining == 0
            push!(out, copy(chosen))
            return
        end
        for j in first:(n - remaining + 1)
            push!(chosen, j)
            visit(j + 1, remaining - 1)
            pop!(chosen)
        end
    end
    visit(1, k)
    return out
end


# Compare N random integer matrices with N samples from the hybrid sampler.
# For each sample, extract the nonbases and group by matroid isomorphism.
# The output is saved as CSV and representative-matrix TSV files.
# Exact isomorphism testing gets expensive as n increases.

function subset_mask(S)
    out = UInt64(0)
    for i in S
        out |= UInt64(1) << (i - 1)
    end
    return out
end

struct MatroidData
    nonbases::Set{UInt64}
    one::Vector{Int}
    two::Matrix{Int}
    three::Dict{UInt64, Int}
    fingerprint::String
    labelled_key::String
end

function matroid_data(A::Matrix{QQ}, subsets)
    k, n = size(A)
    n <= 62 || error("Benchmark supports at most 62 columns")
    nonbases = Set{UInt64}()
    one = zeros(Int, n)
    two = zeros(Int, n, n)
    three = Dict{UInt64, Int}()
    for B in subsets
        iszero(exact_det(A[:, B])) || continue
        push!(nonbases, subset_mask(B))
        for i in B
            one[i] += 1
        end
        for a in 1:(k - 1), b in (a + 1):k
            i, j = B[a], B[b]
            two[i, j] += 1
            two[j, i] += 1
        end
        for a in 1:(k - 2), b in (a + 1):(k - 1), c in (b + 1):k
            key = subset_mask((B[a], B[b], B[c]))
            three[key] = get(three, key, 0) + 1
        end
    end
    # The following is a genuine isomorphism invariant: multiset of
    # individual element signatures (including pair/triple profiles).
    vertex = String[]
    for i in 1:n
        pair_profile = sort([two[i, j] for j in 1:n if j != i])
        triple_profile = Int[]
        for j in 1:(n - 1), ell in (j + 1):n
            if j != i && ell != i
                push!(triple_profile, get(three, subset_mask((i, j, ell)), 0))
            end
        end
        sort!(triple_profile)
        push!(vertex, string(one[i], ":", join(pair_profile, ","), ":",
                             join(triple_profile, ",")))
    end
    fingerprint = string(length(nonbases), "/", join(sort(vertex), "|"))
    labelled_key = join(sort!(collect(nonbases)), ",")
    return MatroidData(nonbases, one, two, three, fingerprint, labelled_key)
end

# Exact matroid isomorphism test by backtracking over column permutations.
# Element/pair/triple invariants prune the search.
function isomorphic(a::MatroidData, b::MatroidData, k::Int, n::Int)
    length(a.nonbases) == length(b.nonbases) || return false
    a.nonbases == b.nonbases && return true
    a.fingerprint == b.fingerprint || return false

    function vertex_colors(d::MatroidData)
        colors = String[]
        for i in 1:n
            pairs = sort([d.two[i, j] for j in 1:n if j != i])
            triples = Int[]
            for j in 1:(n - 1), ell in (j + 1):n
                if j != i && ell != i
                    push!(triples, get(d.three, subset_mask((i, j, ell)), 0))
                end
            end
            push!(colors, string(d.one[i], ":", join(pairs, ","), ":",
                                 join(sort!(triples), ",")))
        end
        return colors
    end
    ca, cb = vertex_colors(a), vertex_colors(b)
    options = [[j for j in 1:n if ca[i] == cb[j]] for i in 1:n]
    any(isempty, options) && return false
    order = sortperm(1:n; by = i -> (length(options[i]), -a.one[i]))
    mapping = zeros(Int, n)
    used = falses(n)

    function mapped_mask(mask::UInt64)
        out = UInt64(0)
        s = mask
        while s != 0
            i = trailing_zeros(s) + 1
            mapping[i] == 0 && return nothing
            out |= UInt64(1) << (mapping[i] - 1)
            s &= s - UInt64(1)
        end
        return out
    end

    function search(t::Int)
        t > n && return true
        i = order[t]
        for j in options[i]
            used[j] && continue
            okay = true
            for u in 1:(t - 1)
                h = order[u]
                if a.two[i, h] != b.two[j, mapping[h]]
                    okay = false
                    break
                end
                for v in 1:(u - 1)
                    h2 = order[v]
                    mask_a = subset_mask((i, h, h2))
                    mask_b = subset_mask((j, mapping[h], mapping[h2]))
                    if get(a.three, mask_a, 0) != get(b.three, mask_b, 0)
                        okay = false
                        break
                    end
                end
                okay || break
            end
            okay || continue
            mapping[i] = j
            used[j] = true
            # Any fully mapped nonbasis must still be a nonbasis.
            # Equal nonbasis counts make this sufficient at t == n.
            for mask in a.nonbases
                out = mapped_mask(mask)
                if out !== nothing && !(out in b.nonbases)
                    okay = false
                    break
                end
            end
            if okay && search(t + 1)
                return true
            end
            mapping[i] = 0
            used[j] = false
        end
        return false
    end
    return search(1)
end

mutable struct ClassTracker
    groups::Dict{String, Vector{Int}}
    records::Vector{MatroidData}
    frequencies::Vector{Int}
    labelled_seen::Set{String}
end
ClassTracker() = ClassTracker(Dict{String,Vector{Int}}(), MatroidData[], Int[], Set{String}())

function record_class!(T::ClassTracker, d::MatroidData, k::Int, n::Int)
    push!(T.labelled_seen, d.labelled_key)
    group = get!(T.groups, d.fingerprint, Int[])
    for classid in group
        if isomorphic(d, T.records[classid], k, n)
            T.frequencies[classid] += 1
            return classid, false
        end
    end
    push!(T.records, d)
    push!(T.frequencies, 1)
    classid = length(T.records)
    push!(group, classid)
    return classid, true
end

# Benchmark: N baseline samples and N hybrid samples.
# Writes per-sample CSV and one TSV per method containing the
# exact representing matrix of each newly discovered class.
function benchmark(N::Int, k::Int, n::Int;
    seed::Int = 2026,
    bound::Int = 1000,
    p_stop::Float64 = 0.30,
    max_steps::Int = 12,
    start_weights = (0.90, 0.08, 0.02),
    step_weights = (0.45, 0.35, 0.20),
    prefix::String = "matroid_test",
    progress_every::Int = 0)

    N > 0 || error("N must be positive")
    n <= 62 || error("n must be <= 62 for benchmark bit masks")
    subsets = k_subsets(n, k)
    println("Benchmark: $N matrices per method, k=$k, n=$n")
    summaryname = "$(prefix)_summary_k$(k)_n$(n).csv"
    open(summaryname, "w") do io
        println(io, "method,samples,k,n,classes,labelled,nonuniform,mean_steps,singleton_classes,max_class_frequency,generation_seconds,extraction_seconds,classification_seconds,total_seconds,seconds_per_class")
    end

    for (method_no, method) in enumerate((:baseline, :hybrid))
        rng = MersenneTwister(seed + method_no - 1)
        tracker = ClassTracker()
        count_nonuniform = 0
        total_steps = 0
        gen_time = 0.0
        extract_time = 0.0
        classify_time = 0.0
        csvname = "$(prefix)_$(method)_k$(k)_n$(n).csv"
        tsvname = "$(prefix)_$(method)_representatives_k$(k)_n$(n).tsv"

        open(csvname, "w") do io
            open(tsvname, "w") do reps
                println(io, "sample,class_id,new_class,unique_classes,distinct_labelled,nonbases,steps,start_mode,operations,generation_seconds,extraction_seconds,classification_seconds,cumulative_seconds")
                println(reps, "class_id\tsample\tmatrix_rows_separated_by_semicolons")
                for s in 1:N
                    t0 = time_ns()
                    details = if method == :baseline
                        A = random_matrix(k, n; rng=rng, mode=:wide, bound=bound)
                        (matrix=A, start_mode=:wide, operations=Symbol[], steps=0)
                    else
                        sample_matroid(k, n; rng=rng, bound=bound,
                                       p_stop=p_stop, max_steps=max_steps,
                                       start_weights=start_weights,
                                       step_weights=step_weights,
                                       return_details=true)
                    end
                    t1 = time_ns()
                    d = matroid_data(details.matrix, subsets)
                    t2 = time_ns()
                    classid, newclass = record_class!(tracker, d, k, n)
                    t3 = time_ns()
                    dt_gen = (t1 - t0) / 1e9
                    dt_extract = (t2 - t1) / 1e9
                    dt_classify = (t3 - t2) / 1e9
                    gen_time += dt_gen
                    extract_time += dt_extract
                    classify_time += dt_classify
                    count_nonuniform += !isempty(d.nonbases)
                    total_steps += details.steps
                    operations = join(string.(details.operations), "|")
                    println(io, join((s, classid, Int(newclass), length(tracker.records),
                                      length(tracker.labelled_seen), length(d.nonbases),
                                      details.steps, details.start_mode, operations,
                                      dt_gen, dt_extract, dt_classify, gen_time+extract_time+classify_time), ","))
                    if progress_every > 0 && s % progress_every == 0
                        println("$method: $s / $N samples, $(length(tracker.records)) classes")
                    end
                    if newclass
                        A = details.matrix
                        rows = [join(string.(A[i, :]), ",") for i in 1:k]
                        println(reps, "$(classid)\t$(s)\t$(join(rows, ";"))")
                    end
                end
            end
        end

        classes = length(tracker.records)
        elapsed = gen_time + extract_time + classify_time
        println("\n--- $method ---")
        @printf("distinct isomorphism classes: %d\n", classes)
        @printf("distinct labelled matroids: %d\n", length(tracker.labelled_seen))
        @printf("nonuniform samples: %d / %d (%.2f%%)\n", count_nonuniform, N,
                100 * count_nonuniform / N)
        @printf("mean successful dependency steps: %.3f\n", total_steps / N)
        @printf("singleton classes: %d\n", count(==(1), tracker.frequencies))
        @printf("largest class frequency: %d\n", maximum(tracker.frequencies))
        @printf("sampling time: %.3f s\n", gen_time)
        @printf("matroid extraction time: %.3f s\n", extract_time)
        @printf("isomorphism classification time: %.3f s\n", classify_time)
        @printf("total measured time: %.3f s\n", elapsed)
        @printf("seconds per discovered class: %.5f\n", elapsed / max(classes, 1))
        open(summaryname, "a") do io
            println(io, join((method, N, k, n, classes,
                              length(tracker.labelled_seen), count_nonuniform,
                              total_steps / N, count(==(1), tracker.frequencies),
                              maximum(tracker.frequencies), gen_time, extract_time,
                              classify_time, elapsed, elapsed / max(classes, 1)), ","))
        end
        println("Per-sample data: $csvname")
        println("Representative matrices: $tsvname")
    end
    println("\nComparison summary: $summaryname")
    return nothing
end

# At the Julia REPL, in the repository directory:
# include("benchmark_matroids.jl")
# benchmark(100, 3, 6; prefix="small_test")
# benchmark(1000, 5, 10; prefix="test_5_10", progress_every=100)
#
# This file also loads sample_matroid() for standalone sampling.
