
nbranch(t::Trace) = nbranch(flatten(t))
function nbranch(stream)
    count = 0
    for (f, _, _) in stream
        if f == assert
            count+=1
        end
    end
    return count
end

function cut_at_nth_branch(stream, nth_branch)
    cut_stream = Tuple{Any, Any, Tuple}[]
    count = 0
    for (f, ret, args) in stream
        push!(cut_stream, (f, ret, args))
        if f == assert
            count += 1
            if count == nth_branch
                return cut_stream
            end
        end
    end
    return cut_stream
end

function force_and_cut(stream, nth_branch)
    cut_stream = cut_at_nth_branch(stream, nth_branch)
    f, ret, args = pop!(cut_stream)
    @assert f == assert
    @assert ret isa Bool
    push!(cut_stream, (f, !ret, args))
end

function checkStream(stream)
    z3model = symbolic(stream)
    sat, model = runZ3(z3model)
    if sat
       inputs = parseZ3(model)
    else
        inputs = ()
    end

    return sat, inputs
end


import InteractiveUtils: subtypes

function concretize(T::Union{DataType, Union})
    ctypes = Any[]
    types = Any[T]

    while !isempty(types)
        T = pop!(types)
        if isconcretetype(T)
            push!(ctypes, T)
        elseif T isa Union
            push!(types, T.a)
            push!(types, T.b)
        else
            append!(types, subtypes(T))
        end
    end
    return ctypes
end


supported(T::DataType)= false
generate(T::DataType) = error("Can't generate values of $T")

const INTEGERS = Union{Bool, Int128, UInt128, Int64, UInt64, Int32, UInt32, Int16, UInt16, Int8, UInt8}
supported(::Type{T}) where T<:INTEGERS = true
generate(::Type{T}) where T<:INTEGERS = rand(T)

function fuzz(f, argtypes...; maxdepth = typemax(Int64))
    worklist = Any[]
    args_ctypes = map(x->Base.filter(supported, concretize(x)), argtypes)
    for types in Iterators.product(args_ctypes...)
        initial_args = map(generate, types)
        push!(worklist, (0, initial_args, Any[]))
    end
    fuzz_worklist(f, worklist, maxdepth)
end

function fuzz_wargs(f, initial_args...; maxdepth = typemax(Int64))
    worklist = Any[(0, initial_args, Any[])]
    fuzz_worklist(f, worklist, maxdepth)
end

###
#    Iterative breath first tree search
#      - Invalidated earliest branch and use Z3 to generate an example for the
#        opposite branch
#      - explore all sides and iterate through the program to discover all branches
function fuzz_worklist(f, worklist::Vector{Any}, maxdepth)
    tested = Any[] # did not error
    errored = Any[]

    while !isempty(worklist)
        depth, args, rands = pop!(worklist)
        val, _, trace = concolic_execution(f, args...; rands = rands)

        if val isa Exception
            push!(errored, (val, args, rands))
        else
            push!(tested, (val, args, rands))
        end

        stream = filter(trace)
        branches = Any[]
        for n in (depth+1):nbranch(stream)
            cut_stream = force_and_cut(stream, n)
            push!(branches, (n, cut_stream))
        end

        @info "Found $(length(branches)) new branches to explore"

        for (d, branch) in branches
            if d >= maxdepth
                @info "Terminated fuzzing that went to deep" maxdepth
                continue
            end
            sat, inputs = try
                checkStream(branch)
            catch ex
                @error "Error in Z3 run, skipping" exception=ex branch
                continue
            end
            if sat
                args, rands, _ = inputs
                push!(worklist, (d, args, rands))
            end
        end
    end
    tested, errored
end