using Oscar
using SHA: sha256

# The input coordinates are (p, h), in lexicographic subset order.
plucker_triples() = [(a,b,c) for a in 1:4 for b in a+1:5 for c in b+1:6]

plucker_fours() = [(a,b,c,d) for a in 1:3 for b in a+1:4 for c in b+1:5 for d in c+1:6]

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

function mapped_directions(directions, Mt)
    isempty(directions) && return nothing
    mapped = matrix(QQ, directions) * Mt
    rows = [i for i in 1:nrows(mapped) if any(j -> !iszero(mapped[i,j]), 1:ncols(mapped))]
    isempty(rows) && return nothing
    return matrix(QQ, [mapped[i,j] for i in rows, j in 1:ncols(mapped)])
end

function linear_image(P, M)
    base = minimal_faces(P)
    directions = rays_modulo_lineality(P)
    Mt = transpose(M)
    points = matrix(QQ, base.base_points) * Mt
    rays = mapped_directions(directions.rays_modulo_lineality, Mt)
    lines = mapped_directions(base.lineality_basis, Mt)
    return convex_hull(QQ, points, rays, lines)
end

function image_pieces(P, forms=stable_intersection_forms())
    result = typeof(P)[]
    is_feasible(P) || return result
    input_dim = dim(P)
    chosen = zeros(Int, length(forms), ambient_dim(P))

    cuts = [[polyhedron(QQ,
                        reduce(vcat, [permutedims(term - other) for other in candidates]),
                        zeros(Int, length(candidates)))
             for term in candidates] for candidates in forms]

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

# Full-dimensional regions of the homogeneous map suffice. Their closures
# cover the domain, including ties. The image of a region can have lower rank.
function cone_pieces_lp(forms, ray_count, output_lineality; split_only=false)
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
    chosen = zeros(Int, length(forms), d)
    pieces = Polyhedron{QQFieldElem}[]
    regions = Ref(0)
    reused = Ref(0)
    started = time()
    last_report = Ref(started)

    function report()
        now = time()
        if now - last_report[] >= 10
            println(length(cache), " exact LPs, ", regions[], " regions, ",
                    length(pieces), " images so far.")
            flush(stdout)
            last_report[] = now
        end
    end

    function find_interior(rows)
        key = Tuple(sort!(collect(rows)))
        return get!(cache, key) do
            A = [row[j] for row in key, j in 1:d]
            # By homogeneity, any strict solution scales into the box.
            augmented = hcat(A, ones(Int, length(key)))
            domain = polyhedron(QQ, vcat(augmented, bounds),
                                vcat(zeros(Int, length(key)), limits))
            value, point = solve_lp(linear_program(domain, objective))
            return value > 0 ? [point[j] for j in 1:d] : nothing
        end
    end

    function visit(rows, point, coordinate)
        report()
        if coordinate > length(cuts)
            regions[] += 1
            if !split_only
                A = [row[j] for row in collect(rows), j in 1:d]
                region = polyhedron(QQ, A, zeros(Int, length(rows)))
                Mt = transpose(matrix(QQ, chosen))
                directions = rays_modulo_lineality(region)
                rays = mapped_directions(directions.rays_modulo_lineality, Mt)
                lines = mapped_directions(directions.lineality_basis, Mt)
                L = isnothing(lines) ? output_lineality : vcat(output_lineality, lines)
                push!(pieces, convex_hull(QQ, zeros(Int, 1, length(forms)), rays, L))
            end
            return
        end
        for (term, requirements) in cuts[coordinate]
            any(row -> ntuple(j -> -row[j], d) in rows, requirements) && continue
            child_rows = union(rows, requirements)
            child_point = point
            if all(row -> sum(row[j] * point[j] for j in 1:d) < 0, requirements)
                reused[] += 1
            else
                child_point = find_interior(child_rows)
                isnothing(child_point) && continue
            end
            chosen[coordinate, :] = term
            visit(child_rows, child_point, coordinate + 1)
        end
    end

    visit(initial_rows, initial_point, 1)
    return (; pieces, regions=regions[], lp_checks=length(cache),
            reused=reused[], seconds=time()-started)
end

function reduced_cone_image(C, forms; split_only=false)
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
    return cone_pieces_lp(reduced_forms, r, L; split_only)
end

# Test containment in a finite union of closed polyhedra.
function covered_by_union(P, pieces)
    return isnothing(uncovered_region(P, pieces))
end

function uncovered_region(P, pieces)
    is_feasible(P) || return nothing
    d = dim(P)
    candidates = filter(pieces) do Q
        dim(Q) >= d || return false
        overlap = intersect(P, Q)
        is_feasible(overlap) && dim(overlap) == d
    end

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

function missed_point(region, pieces)
    d = dim(region)
    point = collect(relative_interior_point(region))
    while true
        i = findfirst(Q -> point in Q, pieces)
        isnothing(i) && return point
        Q = pieces[i]
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

function fan_path(directory, name)
    path = joinpath(directory, name * ".mrdi")
    isfile(path) && return path
    matches = filter(p -> endswith(basename(p), "-" * name * ".mrdi"),
                     readdir(directory; join=true))
    length(matches) == 1 || error("Expected one $name.mrdi file in $directory.")
    return only(matches)
end

load_fan(directory, name) = Oscar.load(fan_path(directory, name))

function check_rank5_factor(directory)
    rank5 = only(maximal_polyhedra(load_fan(directory, "TGr56")))
    @assert ambient_dim(rank5) == 6 && lineality_dim(rank5) == 6
end

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

# Project orthogonally away from the common coordinate-reweighting space.
# This projection commutes with the ground-set permutations.
function reweighting_projection(subsets)
    L = matrix(QQ, [Int(i in B) for i in 1:6, B in subsets])
    Lt = transpose(L)
    return identity_matrix(QQ, length(subsets)) - Lt * inv(L * Lt) * L
end

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

function fan_orbits(directory, name, subsets)
    cones = collect(maximal_polyhedra(load_fan(directory, name)))
    orbits = cone_orbits(cones, subsets)
    println(name, " orbits (representative => size): ",
            [first(first(orbit)) => length(orbit) for orbit in orbits])
    flush(stdout)
    return (; cones, orbits)
end

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
            raw_pieces = compute_input_cone(rank4.cones[rep], rep, forms)
            # All image cones contain the reweighting space. When that is their
            # entire lineality, quotient rays identify the cone uniquely.
            pieces = Polyhedron{QQFieldElem}[]
            seen = Set{Tuple}()
            for Q in raw_pieces
                if lineality_dim(Q) == 6
                    key = normalized_rays(Q, projection)
                    key in seen && continue
                    push!(seen, key)
                end
                push!(pieces, Q)
            end
            # Publish only a complete checkpoint, even if interrupted during save.
            mktempdir(cache) do temp
                draft = joinpath(temp, basename(path))
                Oscar.save(draft, pieces)
                Base.Filesystem.rename(draft, path)
            end
            println("Saved ", length(pieces), " image pieces for input cone ", rep, ".")
        end
        flush(stdout)
        (; orbit, pieces)
    end
end

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

function full_comparison(directory; cache_dir=joinpath(directory, "stable_intersection_cache"))
    images = representative_images(directory; cache_dir)
    target = fan_orbits(directory, "TGr36", plucker_triples())
    # Target symmetry makes the forward check on the two source representatives sufficient.
    println("Checking representative image pieces lie in the target fan.")
    flush(stdout)
    for image in images, (i, Q) in enumerate(image.pieces)
        any(C -> issubset(Q, C), target.cones) ||
            covered_by_union(Q, target.cones) ||
            error("Image piece $i of input cone $(first(first(image.orbit))) is outside the target fan.")
    end

    pieces = relabelled_images(images)
    covered_indices = Int[]
    excluded_indices = Int[]
    missed_points = Dict{Int,Vector{QQFieldElem}}()
    boundary_covered = Dict{Int,Bool}()
    for orbit in target.orbits
        rep = first(first(orbit))
        C = target.cones[rep]
        println("Checking target cone ", rep, " (orbit size ", length(orbit), ").")
        flush(stdout)
        region = uncovered_region(C, pieces)
        if isnothing(region)
            append!(covered_indices, first.(orbit))
            println("  Fully covered.")
        else
            append!(excluded_indices, first.(orbit))
            witness = missed_point(region, pieces)
            missed_points[rep] = witness
            println("  Missed Plücker vector: ", witness)
            boundary_covered[rep] = all(face -> covered_by_union(face, pieces), facets(Polyhedron, C))
            println("  Entire boundary covered: ", boundary_covered[rep])
        end
        flush(stdout)
    end
    sort!(covered_indices)
    sort!(excluded_indices)
    println("Fully covered maximal target cones: ", length(covered_indices), "/", length(target.cones))
    return (; pieces, covered_indices, excluded_indices, missed_points, boundary_covered)
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

# Example usage from the Julia REPL
# include("stable_intersection.jl")
# fan_dir = expanduser("~/random-matroid-sampling/project_sources")
# triangle_test()
# fan_orbits(fan_dir, "TGr46", plucker_fours())
# @time images = representative_images(fan_dir)  # Compute or reload the two images
# @time result = full_comparison(fan_dir)          # Relabel and check target coverage