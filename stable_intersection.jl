using Oscar

# Stable intersection images. Start with full_comparison at the bottom.
# Main route: load fans -> find orbits -> find regions -> map regions -> check coverage.
# full_comparison organises the run; representative_images handles the source orbits.
# compute_cone_image reduces the input, finds regions and maps their generators.
# target_gap and find_missed_point perform the exact coverage checks.
# Saved objects use Oscar.save/load. Progress files use write/read.

# 1. Load the fans, find their orbits and save completed results

# Load the named fan, allowing the numbered filenames supplied with the project.

function load_fan(directory, name)
    path = joinpath(directory, name * ".mrdi")
    if !isfile(path)
        path = only(filter(p -> endswith(basename(p), "-" * name * ".mrdi"),
                           readdir(directory; join=true)))
    end
    return Oscar.load(path)
end

# Project orthogonally away from the common coordinate-reweighting space.
# This projection commutes with the ground-set permutations.
function reweighting_projection(subsets)
    n = maximum(maximum, subsets)
    L = matrix(QQ, [Int(i in B) for i in 1:n, B in subsets])
    Lt = transpose(L)
    return identity_matrix(QQ, length(subsets)) - Lt * inv(L * Lt) * L
end

# Project away reweighting and rescale the rays so we can compare them exactly.
function normalized_rays(P, projection)
    dirs = rays_modulo_lineality(P).rays_modulo_lineality
    isempty(dirs) && return ()
    R = matrix(QQ, dirs) * projection
    rows = Tuple[]
    for i in 1:nrows(R)
        row = [R[i,j] for j in 1:ncols(R)]
        scale = maximum(abs, row)
        push!(rows, Tuple(row ./ scale))
    end
    return Tuple(sort!(rows))
end

# Order is a pullback: new coordinate B reads old coordinate sigma^{-1}(B).
function coordinate_order(subsets, pullback)
    index = Dict(B => i for (i, B) in enumerate(subsets))
    return [index[Tuple(sort!([pullback[i] for i in B]))] for B in subsets]
end

# Load a fan and find its cone orbits using adjacent transpositions.
# Keep the permutation from each representative to each cone in its orbit.
function fan_orbits(directory, name, subsets)
    cones = collect(maximal_polyhedra(load_fan(directory, name)))
    n = maximum(maximum, subsets)
    projection = reweighting_projection(subsets)
    signatures = [normalized_rays(C, projection) for C in cones]
    index = Dict(signature => i for (i, signature) in enumerate(signatures))

    identity_order = collect(1:n)
    generators = map(1:n-1) do j
        permutation = collect(1:n)
        permutation[j], permutation[j+1] = permutation[j+1], permutation[j]
        coordinate_order(subsets, permutation)
    end
    visited = falses(length(cones))
    orbits = Vector{Pair{Int,Vector{Int}}}[]
    for rep in eachindex(cones)
        visited[rep] && continue
        members = [rep => identity_order]
        visited[rep] = true
        head = 1
        while head <= length(members)
            i, pullback = members[head]
            for (j, order) in enumerate(generators)
                signature = Tuple(sort!([Tuple(ray[k] for k in order)
                                         for ray in signatures[i]]))
                member = index[signature]
                visited[member] && continue
                next_pullback = copy(pullback)
                next_pullback[j], next_pullback[j+1] = pullback[j+1], pullback[j]
                push!(members, member => next_pullback)
                visited[member] = true
            end
            head += 1
        end
        push!(orbits, members)
    end
    println(name, " orbits (representative => size): ",
            [first(first(orbit)) => length(orbit) for orbit in orbits])
    flush(stdout)
    return (; cones, orbits)
end

# Write to a temporary file first so an interrupted write cannot leave a partial checkpoint.
function save_completed(writer, path)
    mktempdir(dirname(path)) do temp
        draft = joinpath(temp, basename(path))
        writer(draft)
        Base.Filesystem.rename(draft, path)
    end
end

# 2. Plücker coordinates and linear maps

# List the k-subsets of 1:n in lexicographic order.
plucker_subsets(k, n) = [Tuple(B) for B in Oscar.combinations(n, k)]

# For each output B, list the forms p[I]+q[J] with I intersect J = B and I union J = 1:n.
# Defaults give the rank-(4,5) intersection on six elements.
function stable_intersection_forms(r=4, s=5, n=6)
    left = plucker_subsets(r, n)
    right = plucker_subsets(s, n)
    right_index = Dict(J => i for (i, J) in enumerate(right))
    forms = Vector{Vector{Int}}[]
    for B in plucker_subsets(r+s-n, n)
        candidates = Vector{Int}[]
        for (i, I) in enumerate(left)
            issubset(B, I) || continue
            J = Tuple(sort!([B...; setdiff(1:n, I)...]))
            row = zeros(Int, length(left) + length(right))
            row[i] = 1
            row[length(left) + right_index[J]] = 1
            push!(candidates, row)
        end
        push!(forms, candidates)
    end
    return forms
end

# Apply the linear map to the rays or lineality generators and drop zero directions.
function mapped_directions(directions, Mt)
    isempty(directions) && return nothing
    mapped = matrix(QQ, directions) * Mt
    rows = [i for i in 1:nrows(mapped) if any(j -> !iszero(mapped[i,j]), 1:ncols(mapped))]
    isempty(rows) && return nothing
    return matrix(QQ, [mapped[i,j] for i in rows, j in 1:ncols(mapped)])
end

# Map the base points, rays and lineality generators, then rebuild the image polyhedron.
function linear_image(P, M)
    base = minimal_faces(P)
    directions = rays_modulo_lineality(P)
    Mt = transpose(M)
    points = matrix(QQ, base.base_points) * Mt
    rays = mapped_directions(directions.rays_modulo_lineality, Mt)
    lines = mapped_directions(base.lineality_basis, Mt)
    return convex_hull(QQ, points, rays, lines)
end

# 3. Find compatible regions using feasibility shortcuts

# A cycle cancels the h coordinates. A nonnegative coefficient sum on every
# input ray contradicts strict feasibility throughout the nonnegative orthant.
function has_incompatible_cycle(rows, added, endpoints, ray_count, n)
    directed = [eltype(added)[] for i in 1:n, j in 1:n]
    for row in rows
        edge = endpoints[row]
        isnothing(edge) || push!(directed[edge...], row)
    end
    for row in added
        edge = endpoints[row]
        isnothing(edge) && continue
        i, j = edge
        for reverse in directed[j, i]
            all(k -> row[k] + reverse[k] >= 0, 1:ray_count) && return true
        end
        for k in 1:n, second in directed[j, k], third in directed[k, i]
            all(l -> row[l] + second[l] + third[l] >= 0, 1:ray_count) && return true
        end
    end
    return false
end

# Try new hyperplane coordinates while keeping the ray coefficients fixed.
# The slack is smaller than the smallest positive cycle weight divided by n.
function hyperplane_witness(rows, endpoints, point, ray_count, n)
    denominator_bound = foldl(lcm, (BigInt(denominator(point[k])) for k in 1:ray_count); init=BigInt(1))
    # A simple cycle has at most n edges; this slack is too small to change its sign.
    scale = (n+1) * denominator_bound
    scaled_p = [(n+1) * BigInt(numerator(point[k])) *
                div(denominator_bound, BigInt(denominator(point[k]))) for k in 1:ray_count]
    weights = Tuple{Int,Int,BigInt}[]
    for row in rows
        edge = endpoints[row]
        isnothing(edge) && continue
        i, j = edge
        weight = -sum(row[k] * scaled_p[k] for k in 1:ray_count) - 1
        push!(weights, (i, j, weight))
    end
    distances = zeros(BigInt, n)
    for _ in 1:n
        changed = false
        for (i, j, weight) in weights
            candidate = distances[j] + weight
            if candidate < distances[i]
                distances[i] = candidate
                changed = true
            end
        end
        if !changed
            h = [QQ((distances[i] - distances[n]) // scale) for i in 1:n-1]
            witness = vcat(point[1:ray_count], h)
            all(row -> sum(a*b for (a,b) in zip(row,witness)) < 0, rows) || return nothing
            return witness
        end
    end
    return nothing
end

# Solve an exact LP for a point satisfying all rows strictly.
# Homogeneity lets us put the variables in a unit box and maximise a common slack.
function strict_interior(rows, d)
    ordered = sort!(collect(rows))
    A = [row[j] for row in ordered, j in 1:d]
    bounds = zeros(Int, 2d+2, d+1)
    for j in 1:d+1
        bounds[2j-1, j] = 1
        bounds[2j, j] = -1
    end
    limits = ones(Int, 2d+2)
    limits[end] = 0
    domain = polyhedron(QQ, vcat(hcat(A, ones(Int, length(rows))), bounds),
                        vcat(zeros(Int, length(rows)), limits))
    lp = linear_program(domain, [zeros(Int, d); 1])
    optimal_value(lp) > 0 || return nothing
    return collect(optimal_vertex(lp))[1:d]
end

# Enumerate compatible minima in ray coefficients and n-1 hyperplane coordinates.
# Return closed inequalities and linear maps, including ties on the boundaries.
function compatible_regions(forms, ray_count; n=6)
    d = length(first(first(forms)))
    Row = NTuple{d,Int}
    choices = Vector{Tuple{Vector{Int},Vector{Row}}}[]
    for terms in forms
        candidates = unique(terms)
        options = Tuple{Vector{Int},Vector{Row}}[]
        for term in candidates
            requirements = Row[]
            for other in candidates
                term == other && continue
                difference = term - other
                push!(requirements, Tuple(difference .÷ foldl(gcd, difference)))
            end
            push!(options, (term, requirements))
        end
        push!(choices, options)
    end
    rows = Set{Row}(Tuple(j == i ? -1 : 0 for j in 1:d) for i in 1:ray_count)
    endpoints = Dict{Row,Union{Nothing,Tuple{Int,Int}}}()
    for options in choices, (_, requirements) in options, row in requirements
        tail = row[ray_count+1:end]
        plus = something(findfirst(==(1), tail), n)
        minus = something(findfirst(==(-1), tail), n)
        endpoints[row] = (plus, minus)
    end
    for row in rows
        endpoints[row] = nothing
    end
    chosen = zeros(Int, length(forms), d)
    regions = Tuple{Matrix{Int},Matrix{Int}}[]
    lp_checks = 0
    cycle_rejections = 0
    repaired = 0
    started = time()
    last_report = started

    # Extend the current choice by one coordinate, pruning impossible branches.
    function visit(rows, point, coordinate)
        if time() - last_report >= 10
            println(length(regions), " regions, ", lp_checks, " exact LPs.")
            flush(stdout)
            last_report = time()
        end
        if coordinate > length(choices)
            A = [row[j] for row in sort!(collect(rows)), j in 1:d]
            push!(regions, (A, copy(chosen)))
            return
        end
        for (term, requirements) in choices[coordinate]
            any(row -> ntuple(j -> -row[j], d) in rows, requirements) && continue
            child_rows = union(rows, requirements)
            child_point = point
            if !all(row -> sum(row[j]*point[j] for j in 1:d) < 0, requirements)
                if has_incompatible_cycle(child_rows, requirements, endpoints, ray_count, n)
                    cycle_rejections += 1
                    continue
                end
                child_point = hyperplane_witness(child_rows, endpoints, point, ray_count, n)
                if isnothing(child_point)
                    lp_checks += 1
                    child_point = strict_interior(child_rows, d)
                    isnothing(child_point) && continue
                else
                    repaired += 1
                end
            end
            chosen[coordinate, :] = term
            visit(child_rows, child_point, coordinate+1)
        end
    end

    visit(rows, QQ.([ones(Int, ray_count); zeros(Int, d-ray_count)]), 1)
    println("Found ", length(regions), " regions in ", round(time()-started; digits=2),
            " s, with ", lp_checks, " exact LPs, ", cycle_rejections,
            " cycle rejections and ", repaired, " hyperplane witnesses.")
    flush(stdout)
    return regions
end

# Express the rank-r input cone using ray coefficients and n-1 hyperplane coordinates.
# Return the reduced forms and the output reweighting directions.
function reduce_input_cone(C, forms; rank=4, n=6)
    rays = matrix(ZZ, rays_modulo_lineality(C).rays_modulo_lineality)
    ray_count = nrows(rays)
    basis = zeros(Int, ray_count+n-1, binomial(n, rank)+n)
    for i in 1:ray_count, j in 1:binomial(n, rank)
        basis[i, j] = Int(rays[i, j])
    end
    for j in 1:n-1
        basis[ray_count+j, binomial(n, rank)+j] = 1
    end
    reduced_forms = [[basis * term for term in candidates] for candidates in forms]
    lineality = matrix(QQ, [Int(i in B) for i in 1:n, B in plucker_subsets(rank-1, n)])
    return reduced_forms, ray_count, lineality
end

# 4. Compute and save the images of representative cones

# Equal projected generator sets give equal images, even with redundant rays.
# Check this cheap signature before asking OSCAR for the extremal rays.
function projected_generators(rays, lines, projection)
    (isnothing(lines) || iszero(lines * projection)) || return nothing
    isnothing(rays) && return ()
    R = rays * projection
    key = Tuple[]
    for i in 1:nrows(R)
        row = [R[i,j] for j in 1:ncols(R)]
        scale = maximum(abs, row)
        iszero(scale) || push!(key, Tuple(row ./ scale))
    end
    return Tuple(sort!(unique!(key)))
end

# Compute one cone image, deduplicating pieces in batches to limit memory use.
# With split_only=true, enumerate the regions without constructing their images.
function compute_cone_image(C; rank=4, n=6, split_only=false)
    forms = stable_intersection_forms(rank, n-1, n)
    reduced, ray_count, lineality = reduce_input_cone(C, forms; rank, n)
    regions = compatible_regions(reduced, ray_count; n)
    pieces = Polyhedron{QQFieldElem}[]
    split_only && return pieces
    projection = reweighting_projection(plucker_subsets(rank-1, n))
    generator_keys = Set{Tuple}()
    ray_keys = Set{Tuple}()
    started = time()
    for first_region in 1:64:length(regions)
        for (A, chosen) in regions[first_region:min(first_region+63, length(regions))]
            region = polyhedron(QQ, A, zeros(Int, size(A, 1)))
            Mt = transpose(matrix(QQ, chosen))
            directions = rays_modulo_lineality(region)
            rays = mapped_directions(directions.rays_modulo_lineality, Mt)
            lines = mapped_directions(directions.lineality_basis, Mt)
            key = projected_generators(rays, lines, projection)
            if !isnothing(key)
                key in generator_keys && continue
                push!(generator_keys, key)
            end
            output_lines = isnothing(lines) ? lineality : vcat(lineality, lines)
            Q = convex_hull(QQ, zeros(Int, 1, size(chosen, 1)), rays, output_lines)
            if lineality_dim(Q) == n
                key = normalized_rays(Q, projection)
                key in ray_keys && continue
                push!(ray_keys, key)
            end
            push!(pieces, Q)
        end
        println("Mapped ", min(first_region+63, length(regions)), "/", length(regions),
                " regions, ", length(pieces), " unique image pieces.")
        flush(stdout)
        GC.gc()
    end
    println("Image construction took ", round(time()-started; digits=2), " s.")
    return pieces
end

# Load or compute the representative images for a rank-r input and a hyperplane.
# Save completed cones in cache_dir; an interrupted cone starts again on the next run.
# Use a new cache_dir when changing input files or the map.
# Older saved images work when cache_dir points to their containing folder.
function representative_images(directory; rank=4, n=6,
        cache_dir=joinpath(directory, "stable_intersection_cache", "rank_$(rank)_n_$(n)"))
    # The hyperplane factor has n free Plücker coordinates; its fan is implicit.
    source = fan_orbits(directory, "TGr$(rank)$(n)", plucker_subsets(rank, n))
    mkpath(cache_dir)
    return map(source.orbits) do orbit
        rep = first(first(orbit))
        path = joinpath(cache_dir, "cone_$rep.mrdi")
        if isfile(path)
            println("Loading saved image for input cone ", rep, ".")
            pieces = Oscar.load(path)
        else
            println("Computing image for input cone ", rep, ".")
            pieces = compute_cone_image(source.cones[rep]; rank, n)
            save_completed(path) do draft
                Oscar.save(draft, pieces)
            end
            println("Saved ", length(pieces), " image pieces for input cone ", rep, ".")
        end
        flush(stdout)
        (; orbit, pieces)
    end
end

# Recover the full image by relabelling coordinates of the representative pieces.
function relabelled_images(images, subsets=plucker_subsets(3, 6))
    n = maximum(maximum, subsets)
    projection = reweighting_projection(subsets)
    pieces = Polyhedron{QQFieldElem}[]
    seen = Set{Tuple}()
    for (image, actions) in zip(images, image_relabellings(images, subsets))
        # Reuse the ray signatures when relabelling each representative image.
        keys = [lineality_dim(Q) == n ? normalized_rays(Q, projection) : nothing
                for Q in image.pieces]
        for action in actions
            order = action.order
            for (Q, key) in zip(image.pieces, keys)
                if !isnothing(key)
                    relabelled = Tuple(sort!([Tuple(ray[j] for j in order) for ray in key]))
                    relabelled in seen && continue
                    push!(seen, relabelled)
                end
                push!(pieces, order == eachindex(order) ? Q : linear_image(Q, action.M))
            end
        end
    end
    println("Constructed ", length(pieces), " relabelled image pieces.")
    flush(stdout)
    return pieces
end

# 5. Coverage and missed points

# Look for a full-dimensional region left over after cutting away the image pieces.
# Dimension here is measured relative to the polyhedron P being checked.
function uncovered_region(P, pieces)
    is_feasible(P) || return nothing
    d = dim(P)
    candidates = filter(pieces) do Q
        dim(Q) >= d || return false
        overlap = intersect(P, Q)
        is_feasible(overlap) && dim(overlap) == d
    end

    return gap_after_cuts(P, candidates, d)
end

# Cut off the next covering piece and recurse on what is left.
function gap_after_cuts(P, candidates, d)
    function find_uncovered(region, first_piece)
        for i in first_piece:length(candidates)
            Q = candidates[i]
            issubset(region, Q) && return nothing
            overlap = intersect(region, Q)
            is_feasible(overlap) && dim(overlap) == d || continue

            # Q's affine hull contains this region's affine hull.
            # Partition the complement by the first facet inequality violated.
            remainder = region
            for H in facets(Q)
                a = collect(Oscar.normal_vector(H))
                b = Oscar.negbias(H)
                inside = polyhedron(QQ, permutedims(a), [b])
                if !issubset(remainder, inside)
                    # Later closed pieces cover the strict side exactly when
                    # they cover its closure, which is this weak halfspace cut.
                    outside = polyhedron(QQ, permutedims(-a), [-b])
                    gap = find_uncovered(intersect(remainder, outside), i + 1)
                    isnothing(gap) || return gap
                    remainder = intersect(remainder, inside)
                end
            end
            return nothing
        end
        return region
    end

    # A finite union of lower-dimensional intersections cannot fill a
    # relatively open hole in the union of the full-dimensional ones.
    return find_uncovered(P, 1)
end

# Move the witness off any lower-dimensional piece that contains it.
function find_missed_point(region, containing_piece)
    d = dim(region)
    point = collect(relative_interior_point(region))
    while true
        Q = containing_piece(point)
        isnothing(Q) && return point
        overlap = intersect(region, Q)
        @assert dim(overlap) < d
        # Keep a full-dimensional half of the gap whose relative interior
        # avoids the affine hull of this lower-dimensional intersection.
        for H in affine_hull(overlap)
            a = collect(Oscar.normal_vector(H))
            b = Oscar.negbias(H)
            a_matrix = permutedims(a)
            low = intersect(region, polyhedron(QQ, a_matrix, [b]))
            high = intersect(region, polyhedron(QQ, -a_matrix, [-b]))
            if dim(low) == d && dim(high) == d
                region = low
                point = collect(relative_interior_point(region))
                break
            end
        end
        @assert !(point in Q)
    end
end

# Build the relabelling and its inverse once per source cone.
function image_relabellings(images, subsets=plucker_subsets(3, 6))
    return map(images) do image
        map(image.orbit) do member
            pullback = last(member)
            order = coordinate_order(subsets, pullback)
            M = matrix(QQ, [Int(j == order[i]) for i in eachindex(order), j in eachindex(order)])
            (; order, inverse=invperm(order), M)
        end
    end
end

# Use row-reduced projected generators as an exact key for a linear span.
function span_key(R)
    k, M = rref(R)
    return Tuple(Tuple(M[i,j] for j in 1:ncols(M)) for i in 1:k)
end

# Compute the span modulo reweighting, including any extra lineality.
function projected_span(Q, projection)
    D = rays_modulo_lineality(Q)
    generators = collect(Iterators.flatten((D.rays_modulo_lineality, D.lineality_basis)))
    R = matrix(QQ, [generators[i][j] for i in eachindex(generators), j in 1:ambient_dim(Q)])
    return span_key(R * projection)
end

# Index image pieces of the same span so most permutations need no intersections.
function image_span_index(images, projection)
    return map(images) do image
        by_span = Dict{Tuple,Vector{Int}}()
        dimensions = Int[]
        equations = []
        for (i, Q) in enumerate(image.pieces)
            push!(dimensions, dim(Q))
            push!(equations, collect(affine_hull(Q)))
            key = projected_span(Q, projection)
            push!(get!(() -> Int[], by_span, key), i)
        end
        (; by_span, dimensions, equations)
    end
end

# Keep only distinct full-dimensional intersections with the current target.
function target_gap(P, images, relabellings, spans, projection)
    d = dim(P)
    candidates = Polyhedron{QQFieldElem}[]
    seen = Set{Tuple}()
    target_rays = [collect(v) for v in rays_modulo_lineality(P).rays_modulo_lineality]
    projected = normalized_rays(P, projection)
    for (image, orders, indexed) in zip(images, relabellings, spans)
        higher = findall(>(d), indexed.dimensions)
        for action in orders
            R = matrix(QQ, [v[i] for v in projected, i in action.inverse])
            key = span_key(R)
            matches = get(indexed.by_span, key, Int[])
            if !isempty(higher)
                generators = [v[action.inverse] for v in target_rays]
                matches = [matches; [i for i in higher if
                    all(H -> all(v -> v in H, generators), indexed.equations[i])]]
            end
            isempty(matches) && continue
            source_target = linear_image(P, transpose(action.M))
            for i in matches
                Q = image.pieces[i]
                issubset(source_target, Q) && return nothing
                overlap = intersect(source_target, Q)
                is_feasible(overlap) && dim(overlap) == d || continue
                # The overlap has the target's exact lineality, so its
                # quotient rays determine it after relabelling.
                key = Tuple(sort!([Tuple(ray[j] for j in action.order)
                                  for ray in normalized_rays(overlap, projection)]))
                key in seen && continue
                push!(seen, key)
                push!(candidates, linear_image(overlap, action.M))
            end
        end
    end
    return gap_after_cuts(P, candidates, d)
end

# Test a witness in source coordinates before constructing a relabelled piece.
function containing_image_piece(point, images, relabellings, spans=nothing)
    for (index, (image, orders)) in enumerate(zip(images, relabellings)), action in orders
        inverse_point = point[action.inverse]
        for (i, Q) in enumerate(image.pieces)
            if !isnothing(spans)
                all(H -> inverse_point in H, spans[index].equations[i]) || continue
            end
            inverse_point in Q && return linear_image(Q, action.M)
        end
    end
    return nothing
end

# Use the affine hulls to shortlist target cones for the forward inclusion check.
function check_image_in_target(images, target, projection=reweighting_projection(plucker_subsets(3, 6)))
    indexed = only(image_span_index([(pieces=target,)], projection))
    total = sum(length(image.pieces) for image in images)
    checked = 0
    for image in images, (i, Q) in enumerate(image.pieces)
        d = dim(Q)
        generators = rays_modulo_lineality(Q)
        directions = [collect(v) for v in Iterators.flatten((generators.rays_modulo_lineality,
                                                            generators.lineality_basis))]
        matches = get(indexed.by_span, projected_span(Q, projection), Int[])
        candidates = [target[j] for j in matches]
        if !any(C -> issubset(Q, C), candidates)
            higher = findall(>(d), indexed.dimensions)
            for j in higher
                all(H -> all(v -> v in H, directions), indexed.equations[j]) || continue
                push!(candidates, target[j])
                issubset(Q, target[j]) && break
            end
            any(C -> issubset(Q, C), candidates) || isnothing(uncovered_region(Q, candidates)) ||
                error("Image piece $i of input cone $(first(first(image.orbit))) is outside the target fan.")
        end
        checked += 1
        if checked % 100 == 0
            println("  Checked ", checked, "/", total, " representative image pieces.")
            flush(stdout)
        end
    end
end

# 6. Complete comparison

# Check forward inclusion, target coverage, missed points and boundary coverage.
# Coverage results are readable text beside the saved images.
# Set materialize=true to also construct all relabelled image pieces.
function full_comparison(directory; rank=4, n=6,
        cache_dir=joinpath(directory, "stable_intersection_cache", "rank_$(rank)_n_$(n)"),
        materialize=false)
    images = representative_images(directory; rank, n, cache_dir)
    subsets = plucker_subsets(rank-1, n)
    target = fan_orbits(directory, "TGr$(rank-1)$(n)", subsets)
    checks = mkpath(joinpath(cache_dir, "coverage"))
    projection = reweighting_projection(subsets)
    if !isfile(joinpath(checks, "forward.txt"))
        println("Checking representative images lie in the target fan.")
        check_image_in_target(images, target.cones, projection)
        save_completed(joinpath(checks, "forward.txt")) do draft
            write(draft, "All representative image pieces lie in the target fan.\n")
        end
    end
    coverage_data = nothing
    covered_indices = Int[]
    excluded_indices = Int[]
    missed_points = Dict{Int,Vector{QQFieldElem}}()
    boundary_covered = Dict{Int,Bool}()
    for orbit in target.orbits
        rep = first(first(orbit))
        C = target.cones[rep]
        println("Checking target cone ", rep, " (orbit size ", length(orbit), ").")
        path = joinpath(checks, "target_$rep.txt")
        if !isfile(path)
            if isnothing(coverage_data)
                coverage_data = (image_relabellings(images, subsets), image_span_index(images, projection))
            end
            relabellings, spans = coverage_data
            region = target_gap(C, images, relabellings, spans, projection)
            text = "covered"
            if !isnothing(region)
                witness = find_missed_point(region,
                    p -> containing_image_piece(p, images, relabellings, spans))
                boundary = all(face -> isnothing(target_gap(face, images, relabellings, spans, projection)),
                               facets(Polyhedron, C))
                text = join(["missed", string(boundary), string.(witness)...], "\n")
            end
            save_completed(path) do draft
                write(draft, text)
            end
        end
        saved = split(read(path, String), '\n')
        if first(saved) == "covered"
            append!(covered_indices, first.(orbit))
            println("  Fully covered.")
        else
            append!(excluded_indices, first.(orbit))
            witness = [QQ(parse(Rational{BigInt}, replace(x, "//" => "/"))) for x in saved[3:end]]
            missed_points[rep] = witness
            boundary_covered[rep] = parse(Bool, saved[2])
            println("  Missed Plücker vector: ", witness)
            println("  Entire boundary covered: ", boundary_covered[rep])
        end
        flush(stdout)
    end
    sort!(covered_indices)
    sort!(excluded_indices)
    println("Fully covered maximal target cones: ", length(covered_indices), "/", length(target.cones))
    pieces = materialize ? relabelled_images(images, subsets) : nothing
    return (; pieces, images, covered_indices, excluded_indices, missed_points, boundary_covered)
end

# Example usage from the Julia REPL.
# include("stable_intersection.jl")
# fan_dir = abspath("project_sources")
# The optional triangle example is in stable_intersection_examples.jl.
# @time images = representative_images(fan_dir);
# @time result = full_comparison(fan_dir);
# @time result = full_comparison(fan_dir; materialize=true);
# Oscar.save("factorisable_image_TGr36.mrdi", result.pieces)
# pieces = Oscar.load("factorisable_image_TGr36.mrdi")
# The general form builder accepts (r,s,n). The optimised fan workflow uses s=n-1.
