using Oscar
using SHA: sha256
using Serialization: serialize, deserialize

# 1. Plücker coordinates and the linear maps

# The input coordinates are (p, h), in lexicographic subset order.
# List the rank-3 output coordinates in lexicographic order.
plucker_triples() = [(a,b,c) for a in 1:4 for b in a+1:5 for c in b+1:6]

# List the rank-4 input coordinates in lexicographic order.
plucker_fours() = [(a,b,c,d) for a in 1:3 for b in a+1:4 for c in b+1:5 for d in c+1:6]

# For each triple B, build the three forms p[B ∪ {i}] + h[[6] ∖ {i}].
# The B-coordinate of the stable intersection is the minimum of these forms.
function stable_intersection_forms()
    fours = plucker_fours()
    fives = sort([Tuple(i for i in 1:6 if i != j) for j in 1:6])
    p_index = Dict(A => i for (i,A) in enumerate(fours))
    h_index = Dict(A => i for (i,A) in enumerate(fives))
    forms = Vector{Vector{Int}}[]
    for B in plucker_triples()
        candidates = Vector{Int}[]
        for i in setdiff(1:6, B)
            row = zeros(Int, 21)
            row[p_index[Tuple(sort!([B..., i]))]] = 1
            row[15 + h_index[Tuple(j for j in 1:6 if j != i)]] = 1
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

# Split an input polyhedron by the minimising terms and map each resulting piece.
function image_pieces(P, forms=stable_intersection_forms())
    result = typeof(P)[]
    is_feasible(P) || return result
    input_dim = dim(P)
    chosen = zeros(Int, length(forms), ambient_dim(P))

    cuts = [[polyhedron(QQ,
                        reduce(vcat, [permutedims(term - other) for other in candidates]),
                        zeros(Int, length(candidates)))
             for term in candidates] for candidates in forms]

    # Choose a minimiser in the next coordinate and recurse on the resulting pieces.
    function visit(region, coordinate)
        if coordinate > length(forms)
            push!(result, linear_image(region, matrix(QQ, chosen)))
            return
        end
        # If a term is already minimal throughout the region, no split is needed.
        for j in eachindex(cuts[coordinate])
            if issubset(region, cuts[coordinate][j])
                chosen[coordinate, :] = forms[coordinate][j]
                visit(region, coordinate + 1)
                return
            end
        end
        for j in eachindex(cuts[coordinate])
            child = intersect(region, cuts[coordinate][j])
            # The closed children of full input dimension cover the parent.
            if is_feasible(child) && dim(child) == input_dim
                chosen[coordinate, :] = forms[coordinate][j]
                visit(child, coordinate + 1)
            end
        end
    end

    visit(P, 1)
    return result
end

# 2. Find the compatible regions

# Group coordinates with shared comparisons so contradictions can appear earlier.
function overlapping_order(forms, ray_count)
    supports = [Set(findfirst(!iszero, term[ray_count+1:end]) for term in terms)
                for terms in forms]
    remaining = collect(eachindex(forms))
    order = Int[]
    while !isempty(remaining)
        scores = [sum((length(intersect(supports[i], supports[j]))^2 for j in order); init=0)
                  for i in remaining]
        push!(order, splice!(remaining, argmax(scores)))
    end
    return order
end

# Identify a comparison h_i - h_j plus terms in the rank-4 ray coefficients.
# The sixth h coordinate is fixed at zero in the reduced search.
function comparison_endpoints(row, ray_count)
    tail = row[ray_count+1:end]
    plus = findfirst(==(1), tail)
    minus = findfirst(==(-1), tail)
    count(!iszero, tail) == Int(!isnothing(plus)) + Int(!isnothing(minus)) || return nothing
    (isnothing(plus) && isnothing(minus)) && return nothing
    return something(plus, 6), something(minus, 6)
end

# A cycle cancels the h coordinates. A nonnegative coefficient sum on every
# input ray contradicts strict feasibility throughout the nonnegative orthant.
function has_incompatible_cycle(rows, added, endpoints, ray_count)
    directed = [eltype(added)[] for i in 1:6, j in 1:6]
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
        for k in 1:6, second in directed[j, k], third in directed[k, i]
            all(l -> row[l] + second[l] + third[l] >= 0, 1:ray_count) && return true
        end
    end
    return false
end

# Try new hyperplane coordinates while keeping the current rank-4 input fixed.
# The slack is smaller than the smallest positive cycle weight divided by six.
function hyperplane_witness(rows, endpoints, point, ray_count)
    denominator_bound = foldl(lcm, (BigInt(denominator(point[k])) for k in 1:ray_count))
    scale = 7 * denominator_bound
    scaled_p = [7 * BigInt(numerator(point[k])) *
                div(denominator_bound, BigInt(denominator(point[k]))) for k in 1:ray_count]
    weights = Tuple{Int,Int,BigInt}[]
    for row in rows
        edge = endpoints[row]
        isnothing(edge) && continue
        i, j = edge
        weight = -sum(row[k] * scaled_p[k] for k in 1:ray_count) - 1
        push!(weights, (i, j, weight))
    end
    distances = zeros(BigInt, 6)
    for _ in 1:6
        changed = false
        for (i, j, weight) in weights
            candidate = distances[j] + weight
            if candidate < distances[i]
                distances[i] = candidate
                changed = true
            end
        end
        if !changed
            h = [QQ((distances[i] - distances[6]) // scale) for i in 1:5]
            witness = vcat(point[1:ray_count], h)
            all(row -> sum(a*b for (a,b) in zip(row,witness)) < 0, rows) || return nothing
            return witness
        end
    end
    return nothing
end

# Full-dimensional regions of the homogeneous map suffice. Their closures
# cover the domain, including ties. The image of a region can have lower rank.
function cone_pieces_lp(forms, ray_count, output_lineality; split_only=false, on_region=nothing, reorder=false, cycle_pruning=false, repair_h=false, first_branch=1, on_branch=nothing)
    d = length(first(first(forms)))
    Row = NTuple{d,Int}
    cuts = Vector{Tuple{Vector{Int},Vector{Row}}}[]
    for forms_at_coordinate in forms
        candidates = unique(forms_at_coordinate)
        choices = Tuple{Vector{Int},Vector{Row}}[]
        for term in candidates
            requirements = Row[]
            for other in candidates
                term == other && continue
                difference = term - other
                push!(requirements, Tuple(difference .÷ foldl(gcd, difference)))
            end
            push!(choices, (term, requirements))
        end
        push!(cuts, choices)
    end
    initial_rows = Set{Row}(
        Tuple(j == i ? -1 : 0 for j in 1:d) for i in 1:ray_count
    )
    order = reorder ? overlapping_order(forms, ray_count) : collect(eachindex(forms))
    use_cycles = cycle_pruning && d - ray_count == 5
    endpoints = Dict{Row,Union{Nothing,Tuple{Int,Int}}}(row => comparison_endpoints(row, ray_count)
                     for choices in cuts for (_, requirements) in choices for row in requirements)
    for row in initial_rows
        endpoints[row] = nothing
    end
    cycle_rejections = Ref(0)
    repaired = Ref(0)
    initial_point = QQ.([ones(Int, ray_count); zeros(Int, d - ray_count)])
    objective = [zeros(Int, d); 1]
    bounds = zeros(Int, 2d + 2, d + 1)
    for j in 1:d+1
        bounds[2j - 1, j] = 1
        bounds[2j, j] = -1
    end
    limits = ones(Int, 2d + 2)
    limits[end] = 0
    cache = Dict{Tuple,Union{Nothing,Vector{QQFieldElem}}}()
    lp_checks = Ref(0)
    chosen = zeros(Int, length(forms), d)
    pieces = Polyhedron{QQFieldElem}[]
    regions = Ref(0)
    reused = Ref(0)
    started = time()
    last_report = Ref(started)

    # Print progress every ten seconds or so during enumeration.
    function report()
        now = time()
        if now - last_report[] >= 10
            println(lp_checks[], " exact LPs, ", regions[], " regions, ",
                    length(pieces), " images so far.")
            flush(stdout)
            last_report[] = now
        end
    end

    # Use an exact LP to find a point where all the current inequalities are strict.
    function find_interior(rows)
        key = Tuple(sort!(collect(rows)))
        if length(cache) >= 512 && !haskey(cache, key)
            empty!(cache)
        end
        return get!(cache, key) do
            lp_checks[] += 1
            A = [row[j] for row in key, j in 1:d]
            # By homogeneity, any strict solution scales into the box.
            augmented = hcat(A, ones(Int, length(key)))
            domain = polyhedron(QQ, vcat(augmented, bounds),
                                vcat(zeros(Int, length(key)), limits))
            lp = linear_program(domain, objective)
            optimal_value(lp) > 0 || return nothing
            point = optimal_vertex(lp)
            return [point[j] for j in 1:d]
        end
    end

    # Extend a partial choice of minimisers, reusing the interior point when it still works.
    function visit(rows, point, coordinate)
        report()
        if coordinate > length(cuts)
            regions[] += 1
            if !isnothing(on_region) || !split_only
                A = [row[j] for row in sort!(collect(rows)), j in 1:d]
                if isnothing(on_region)
                    push!(pieces, region_image(A, chosen, output_lineality))
                else
                    on_region(A, chosen)
                end
            end
            return
        end
        output_coordinate = order[coordinate]
        for (index, (term, requirements)) in enumerate(cuts[output_coordinate])
            coordinate == 1 && index < first_branch && continue
            any(row -> ntuple(j -> -row[j], d) in rows, requirements) && continue
            child_rows = union(rows, requirements)
            child_point = point
            if all(row -> sum(row[j] * point[j] for j in 1:d) < 0, requirements)
                reused[] += 1
            else
                if use_cycles && has_incompatible_cycle(child_rows, requirements, endpoints, ray_count)
                    cycle_rejections[] += 1
                    continue
                end
                child_point = repair_h && d - ray_count == 5 ?
                    hyperplane_witness(child_rows, endpoints, point, ray_count) : nothing
                if isnothing(child_point)
                    child_point = find_interior(child_rows)
                    isnothing(child_point) && continue
                else
                    repaired[] += 1
                end
            end
            chosen[output_coordinate, :] = term
            visit(child_rows, child_point, coordinate + 1)
            if coordinate == 1 && !isnothing(on_branch)
                on_branch(index)
            end
        end
    end

    visit(initial_rows, initial_point, 1)
    return (; pieces, regions=regions[], lp_checks=lp_checks[],
            reused=reused[], cycle_rejections=cycle_rejections[], repaired=repaired[],
            seconds=time()-started)
end

# 3. Build the image of each region

# Apply the region's linear map to its rays and lineality generators.
function mapped_region(A, chosen)
    region = polyhedron(QQ, A, zeros(Int, size(A, 1)))
    Mt = transpose(matrix(QQ, chosen))
    directions = rays_modulo_lineality(region)
    rays = mapped_directions(directions.rays_modulo_lineality, Mt)
    lines = mapped_directions(directions.lineality_basis, Mt)
    return rays, lines
end

# Map the closed region for one choice of minimisers and restore output lineality.
function region_image(A, chosen, output_lineality)
    rays, lines = mapped_region(A, chosen)
    L = isnothing(lines) ? output_lineality : vcat(output_lineality, lines)
    return convex_hull(QQ, zeros(Int, 1, size(chosen, 1)), rays, L)
end

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

# Use the rank-4 ray coefficients and five free hyperplane coordinates for the search.
function reduced_cone_image(C, forms; split_only=false, on_region=nothing, reorder=false, cycle_pruning=false, repair_h=false, first_branch=1, on_branch=nothing)
    @assert ambient_dim(C) == 15 && lineality_dim(C) == 6
    rays = matrix(ZZ, rays_modulo_lineality(C).rays_modulo_lineality)
    r = nrows(rays)
    @assert r > 0
    basis = zeros(Int, r + 5, 21)
    for i in 1:r, j in 1:15
        basis[i, j] = Int(rays[i, j])
    end
    for j in 1:5
        basis[r + j, 15 + j] = 1
    end
    reduced_forms = [[basis * term for term in candidates] for candidates in forms]
    # Simultaneous input reweighting restores these output directions.
    L = matrix(QQ, [Int(i in B) for i in 1:6, B in plucker_triples()])
    return cone_pieces_lp(reduced_forms, r, L; split_only, on_region, reorder, cycle_pruning,
                          repair_h, first_branch, on_branch)
end

# 4. Check a polyhedral union and find a missed point

# Test containment in a finite union of closed polyhedra.
function covered_by_union(P, pieces)
    return isnothing(uncovered_region(P, pieces))
end

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

# Find a point in the gap and check it against every piece, including lower-dimensional ones.
function missed_point(region, pieces)
    return find_missed_point(region, point -> begin
        i = findfirst(Q -> point in Q, pieces)
        isnothing(i) ? nothing : pieces[i]
    end)
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

# Check the triangle-and-tail example and verify that the code finds a missed point.
function triangle_test()
    triangle = convex_hull(QQ, [-2 1; 0 1; 0 -1])
    embed = zero_matrix(QQ, 21, 2)
    embed[21, 1] = 1  # h_23456
    embed[20, 2] = 1  # h_13456
    pieces = image_pieces(linear_image(triangle, embed))
    project = zero_matrix(QQ, 2, 20)
    triples = plucker_triples()
    project[1, only(findall(==((2,5,6)), triples))] = 1
    project[2, only(findall(==((1,5,6)), triples))] = 1
    projected = [linear_image(Q, project) for Q in pieces]

    expected = [convex_hull(QQ, [-1 0; 0 0; 0 -1]),
                convex_hull(QQ, [-2 0; -1 0])]
    @assert all(Q -> covered_by_union(Q, projected), expected)
    @assert all(Q -> covered_by_union(Q, expected), projected)
    # The segment between two attained points crosses a gap in the image.
    bridge = convex_hull(QQ, [-2 0; 0 -1])
    gap = uncovered_region(bridge, projected)
    @assert !isnothing(gap)
    witness = missed_point(gap, projected)
    @assert witness in bridge
    @assert all(Q -> !(witness in Q), projected)
    println("Triangle-and-tail test passed.")
end

# 5. Load the fans and run a single input cone

# Find the saved fan, allowing a filename prefix before TGr.
function fan_path(directory, name)
    path = joinpath(directory, name * ".mrdi")
    isfile(path) && return path
    matches = filter(p -> endswith(basename(p), "-" * name * ".mrdi"),
                     readdir(directory; join=true))
    length(matches) == 1 || error("Expected one $name.mrdi file in $directory.")
    return only(matches)
end

# Load the fan from its OSCAR file. OSCAR 1.8.2 cannot resolve the
# development-version metadata on the supplied TGr36 file, but its enclosed
# rational polymake complex can be read directly.
function load_fan(directory, name)
    path = fan_path(directory, name)
    try
        return Oscar.load(path)
    catch error
        error isa MethodError && error.f === (+) && error.args == (nothing, 1) || rethrow()
        data = Oscar.Serialization.JSON.parsefile(path)
        startswith(data["_ns"]["Oscar"][2], "1.9.0-DEV-") || rethrow()
        payload = data["data"]
        payload["_type"] == "fan::PolyhedralComplex<Rational>" || rethrow()
        return Oscar.Serialization.load_from_polymake(Dict{Symbol,Any}(
            Symbol(key) => value for (key, value) in payload))
    end
end

# Check that TGr(5,6) is all of the six-dimensional hyperplane coordinate space.
function check_rank5_factor(directory)
    rank5 = only(maximal_polyhedra(load_fan(directory, "TGr56")))
    @assert ambient_dim(rank5) == 6 && lineality_dim(rank5) == 6
end

# Run the search for one labelled input cone and print the timings and counts.
function compute_input_cone(C, i, forms; split_only=false)
    println("Splitting input cone ", i, ".")
    flush(stdout)
    result = reduced_cone_image(C, forms; split_only)
    println("Input cone ", i, " finished in ", round(result.seconds; digits=2),
            " s. Regions ", result.regions, ", exact LPs ", result.lp_checks,
            ", reused interior points ", result.reused, ", images ",
            length(result.pieces), ".")
    flush(stdout)
    return result.pieces
end

# Compute the images for the requested input cones, or just count their regions.
function input_products(directory, indices; split_only=false)
    rank4 = maximal_polyhedra(load_fan(directory, "TGr46"))
    check_rank5_factor(directory)
    forms = stable_intersection_forms()
    pieces = Polyhedron{QQFieldElem}[]
    for i in indices
        append!(pieces, compute_input_cone(rank4[i], i, forms; split_only))
    end
    return pieces
end

# 6. Reduce by relabelling and save the representative images

# Project orthogonally away from the common coordinate-reweighting space.
# This projection commutes with the ground-set permutations.
function reweighting_projection(subsets)
    L = matrix(QQ, [Int(i in B) for i in 1:6, B in subsets])
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
        iszero(scale) && error("Unexpected ray in the reweighting space.")
        push!(rows, Tuple(row ./ scale))
    end
    return Tuple(sort!(rows))
end

# Order is a pullback: new coordinate B reads old coordinate sigma^{-1}(B).
function coordinate_order(subsets, pullback)
    index = Dict(B => i for (i, B) in enumerate(subsets))
    return [index[Tuple(sort!([pullback[i] for i in B]))] for B in subsets]
end

# Find the cone orbits using adjacent transpositions.
# Keep the permutation from each representative to each cone in its orbit.
function cone_orbits(cones, subsets)
    projection = reweighting_projection(subsets)
    signatures = map(cones) do C
        lineality_dim(C) == 6 || error("Expected six lineality directions.")
        L = matrix(QQ, rays_modulo_lineality(C).lineality_basis)
        iszero(L * projection) || error("Unexpected lineality space in the saved fan.")
        normalized_rays(C, projection)
    end
    index = Dict(signature => i for (i, signature) in enumerate(signatures))
    length(index) == length(cones) || error("The saved fan has duplicate maximal cones.")

    identity_order = collect(1:6)
    generators = [coordinate_order(subsets, [i == j ? j+1 : i == j+1 ? j : i
                                              for i in 1:6]) for j in 1:5]
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
                member = get(index, signature, 0)
                member != 0 || error("The saved fan is not invariant under relabelling.")
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
    return orbits
end

# Load a fan, find its maximal-cone orbits and print their sizes.
function fan_orbits(directory, name, subsets)
    cones = collect(maximal_polyhedra(load_fan(directory, name)))
    orbits = cone_orbits(cones, subsets)
    println(name, " orbits (representative => size): ",
            [first(first(orbit)) => length(orbit) for orbit in orbits])
    flush(stdout)
    return (; cones, orbits)
end

# Write to a temporary file first so an interrupted write cannot leave a partial checkpoint.
function write_checkpoint(writer, path)
    mktempdir(dirname(path)) do temp
        draft = joinpath(temp, basename(path))
        writer(draft)
        Base.Filesystem.rename(draft, path)
    end
end

# Save the compatible regions, then build and deduplicate their images in batches.
# On a rerun, reuse the finished region list and any saved image batches.
function checkpointed_cone_image(C, rep, forms, projection, final_path)
    legacy = joinpath(dirname(final_path), "cone_$(rep)_regions_v1")
    work = isfile(joinpath(legacy, "complete")) ? legacy :
        mkpath(joinpath(dirname(final_path), "cone_$(rep)_regions_v3"))
    done = joinpath(work, "complete")
    if !isfile(done)
        # Batches only count as committed once their top-level branch finishes.
        progress = joinpath(work, "branches")
        last_branch, number = isfile(progress) ? deserialize(progress) : (0, 0)
        println("Enumerating compatible regions for input cone ", rep,
                " after ", last_branch, " completed top-level branches.")
        flush(stdout)
        batch = Tuple{Matrix{Int},Matrix{Int}}[]
        # Write the current batch of region inequalities and linear maps to disk.
        function save_regions()
            isempty(batch) && return
            number += 1
            write_checkpoint(joinpath(work, "regions_$number.bin")) do path
                serialize(path, batch)
            end
            empty!(batch)
        end
        # Publish a finished branch only after all its region batches are on disk.
        function save_branch(index)
            save_regions()
            write_checkpoint(progress) do path
                serialize(path, (index, number))
            end
            println("Saved input cone ", rep, " through top-level branch ", index, ".")
            flush(stdout)
        end
        stats = reduced_cone_image(C, forms; cycle_pruning=true, repair_h=true,
            first_branch=last_branch+1, on_branch=save_branch, on_region=(A, chosen) -> begin
                push!(batch, (A, copy(chosen)))
                length(batch) == 64 && save_regions()
            end)
        println("Enumerated ", stats.regions, " regions this run in ",
                round(stats.seconds; digits=2), " s, with ", stats.lp_checks, " exact LPs, ",
                stats.cycle_rejections, " cycle rejections and ", stats.repaired, " hyperplane witnesses.")
        flush(stdout)
        write_checkpoint(done) do path
            serialize(path, number)
        end
        GC.gc()
    end

    L = matrix(QQ, [Int(i in B) for i in 1:6, B in plucker_triples()])
    seen = Set{Tuple}()
    generator_keys = Set{Tuple}()
    pieces = Polyhedron{QQFieldElem}[]
    count = deserialize(done)
    started = time()
    for i in 1:count
        path = joinpath(work, "images_$i.mrdi")
        if isfile(path)
            filesize(path) == 0 && continue
            for Q in Oscar.load(path)
                lineality_dim(Q) == 6 && push!(seen, normalized_rays(Q, projection))
                push!(pieces, Q)
            end
        else
            batch = Polyhedron{QQFieldElem}[]
            for (A, chosen) in deserialize(joinpath(work, "regions_$i.bin"))
                rays, lines = mapped_region(A, chosen)
                key = projected_generators(rays, lines, projection)
                if !isnothing(key)
                    key in generator_keys && continue
                    push!(generator_keys, key)
                end
                output_lines = isnothing(lines) ? L : vcat(L, lines)
                Q = convex_hull(QQ, zeros(Int, 1, size(chosen, 1)), rays, output_lines)
                if lineality_dim(Q) == 6
                    key = normalized_rays(Q, projection)
                    key in seen && continue
                    push!(seen, key)
                end
                push!(batch, Q)
            end
            write_checkpoint(path) do draft
                if isempty(batch)
                    touch(draft)
                else
                    Oscar.save(draft, batch)
                end
            end
            append!(pieces, batch)
        end
        println("Input cone ", rep, ": image batch ", i, "/", count,
                ", ", length(pieces), " unique pieces.")
        flush(stdout)
        GC.gc()
    end
    println("Image batches took ", round(time()-started; digits=2), " s.")
    flush(stdout)
    write_checkpoint(final_path) do draft
        Oscar.save(draft, pieces)
    end
    return pieces
end

# Load or compute one stable intersection image per rank-4 cone orbit.
function representative_images(directory; cache_dir=joinpath(directory, "stable_intersection_cache"))
    check_rank5_factor(directory)
    rank4 = fan_orbits(directory, "TGr46", plucker_fours())
    # Invalidate checkpoints if either input fan changes.
    fan_hash = bytes2hex(sha256(vcat(read(fan_path(directory, "TGr46")),
                                     read(fan_path(directory, "TGr56")))))
    cache = mkpath(joinpath(cache_dir, "v1-" * fan_hash))
    forms = stable_intersection_forms()
    projection = reweighting_projection(plucker_triples())
    return map(rank4.orbits) do orbit
        rep = first(first(orbit))
        path = joinpath(cache, "cone_$rep.mrdi")
        if isfile(path)
            println("Loading saved image for input cone ", rep, ".")
            pieces = Oscar.load(path)
        else
            pieces = checkpointed_cone_image(rank4.cones[rep], rep, forms,
                                             projection, path)
            println("Saved ", length(pieces), " image pieces for input cone ", rep, ".")
        end
        flush(stdout)
        (; orbit, pieces)
    end
end

# Recover the full image by permuting the rank-3 coordinates of the representative images.
function relabelled_images(images)
    triples = plucker_triples()
    projection = reweighting_projection(triples)
    pieces = Polyhedron{QQFieldElem}[]
    seen = Set{Tuple}()
    for image in images
        # Reuse the ray signatures when relabelling each representative image.
        keys = [lineality_dim(Q) == 6 ? normalized_rays(Q, projection) : nothing
                for Q in image.pieces]
        for (_, pullback) in image.orbit
            order = coordinate_order(triples, pullback)
            M = matrix(QQ, [Int(j == order[i]) for i in eachindex(order), j in eachindex(order)])
            for (Q, key) in zip(image.pieces, keys)
                if !isnothing(key)
                    relabelled = Tuple(sort!([Tuple(ray[j] for j in order) for ray in key]))
                    relabelled in seen && continue
                    push!(seen, relabelled)
                end
                push!(pieces, order == eachindex(order) ? Q : linear_image(Q, M))
            end
        end
    end
    println("Constructed ", length(pieces), " relabelled image pieces.")
    flush(stdout)
    return pieces
end

# 7. Compare the image with the target fan

# Build the relabelling and its inverse once per source cone.
function image_relabellings(images)
    triples = plucker_triples()
    return [[begin
        order = coordinate_order(triples, pullback)
        M = matrix(QQ, [Int(j == order[i]) for i in eachindex(order), j in eachindex(order)])
        (; order, inverse=invperm(order), M)
    end for (_, pullback) in image.orbit] for image in images]
end

# Use row-reduced projected generators as an exact key for a linear span.
function span_key(R)
    k, M = rref(R)
    return Tuple(Tuple(M[i,j] for j in 1:ncols(M)) for i in 1:k)
end


# Build the same span key from a list of rays.
function span_key(rays, width)
    isempty(rays) && return ()
    return span_key(matrix(QQ, [rays[i][j] for i in eachindex(rays), j in 1:width]))
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
            key = span_key([[v[i] for i in action.inverse] for v in projected], ambient_dim(P))
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
function check_image_in_target(images, target)
    projection = reweighting_projection(plucker_triples())
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
            any(C -> issubset(Q, C), candidates) || covered_by_union(Q, candidates) ||
                error("Image piece $i of input cone $(first(first(image.orbit))) is outside the target fan.")
        end
        checked += 1
        if checked % 100 == 0
            println("  Checked ", checked, "/", total, " representative image pieces.")
            flush(stdout)
        end
    end
end

# Compare the image with TGr(3,6), checking one target cone per orbit.
# For an orbit with a gap, return a missed vector and check coverage of the boundary.
function full_comparison(directory; cache_dir=joinpath(directory, "stable_intersection_cache"), materialize=false)
    images = representative_images(directory; cache_dir)
    target = fan_orbits(directory, "TGr36", plucker_triples())
    # Target symmetry makes the forward check on the two source representatives sufficient.
    fan_hash = bytes2hex(sha256(vcat(read(fan_path(directory, "TGr46")),
                                     read(fan_path(directory, "TGr56")),
                                     read(fan_path(directory, "TGr36")))))
    checks = mkpath(joinpath(cache_dir, "coverage-v1-" * fan_hash))
    forward_done = joinpath(checks, "forward")
    if !isfile(forward_done)
        println("Checking representative image pieces lie in the target fan.")
        flush(stdout)
        started = time()
        check_image_in_target(images, target.cones)
        write_checkpoint(touch, forward_done)
        println("Forward inclusion took ", round(time()-started; digits=2), " s.")
        flush(stdout)
    end
    # Only build the search index if there is an unfinished target check.
    coverage_data = nothing
    covered_indices = Int[]
    excluded_indices = Int[]
    missed_points = Dict{Int,Vector{QQFieldElem}}()
    boundary_covered = Dict{Int,Bool}()
    for orbit in target.orbits
        rep = first(first(orbit))
        C = target.cones[rep]
        println("Checking target cone ", rep, " (orbit size ", length(orbit), ").")
        flush(stdout)
        path = joinpath(checks, "target_$rep.bin")
        if isfile(path)
            saved = deserialize(path)
        else
            started = time()
            if isnothing(coverage_data)
                projection = reweighting_projection(plucker_triples())
                coverage_data = (image_relabellings(images), image_span_index(images, projection), projection)
            end
            relabellings, spans, projection = coverage_data
            region = target_gap(C, images, relabellings, spans, projection)
            if isnothing(region)
                saved = (witness=nothing, boundary=true)
            else
                witness = find_missed_point(region,
                    p -> containing_image_piece(p, images, relabellings, spans))
                boundary = all(face -> isnothing(target_gap(face, images, relabellings, spans, projection)),
                               facets(Polyhedron, C))
                saved = (; witness=string.(witness), boundary)
            end
            write_checkpoint(path) do draft
                serialize(draft, saved)
            end
            println("  Coverage check took ", round(time()-started; digits=2), " s.")
        end
        if isnothing(saved.witness)
            append!(covered_indices, first.(orbit))
            println("  Fully covered.")
        else
            append!(excluded_indices, first.(orbit))
            witness = [QQ(parse(Rational{BigInt}, replace(x, "//" => "/")))
                       for x in saved.witness]
            missed_points[rep] = witness
            boundary_covered[rep] = saved.boundary
            println("  Missed Plücker vector: ", witness)
            println("  Entire boundary covered: ", saved.boundary)
        end
        flush(stdout)
    end
    sort!(covered_indices)
    sort!(excluded_indices)
    println("Fully covered maximal target cones: ", length(covered_indices), "/", length(target.cones))
    pieces = materialize ? relabelled_images(images) : nothing
    return (; pieces, images, covered_indices, excluded_indices, missed_points, boundary_covered)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    mode = isempty(ARGS) ? "test" : ARGS[1]
    directory = length(ARGS) >= 2 ? ARGS[2] : joinpath(@__DIR__, "project_sources")
    if mode == "test"
        triangle_test()
    elseif mode in ("split", "one")
        index = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 1
        input_products(directory, index:index; split_only=(mode == "split"))
    elseif mode == "orbits"
        fan_orbits(directory, "TGr46", plucker_fours())
        fan_orbits(directory, "TGr36", plucker_triples())
    elseif mode == "representatives"
        representative_images(directory)
    elseif mode == "all"
        full_comparison(directory)
    else
        error("Use test, split, one, orbits, representatives, or all.")
    end
end

# 8. Example usage from the Julia REPL
# include("stable_intersection.jl")
# fan_dir = expanduser("~/random-matroid-sampling/project_sources")
# triangle_test()
# fan_orbits(fan_dir, "TGr46", plucker_fours())
# @time images = representative_images(fan_dir)  # Compute or reload the two images
# @time result = full_comparison(fan_dir)          # Check coverage without collecting all relabelled pieces
# @time result = full_comparison(fan_dir; materialize=true)  # Also return all relabelled pieces
