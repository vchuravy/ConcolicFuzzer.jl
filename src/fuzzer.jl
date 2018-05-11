
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

generate(::Type{Int64}) = rand(Int)

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

function execute(f, args...; rands = Any[])
    try
        val, _, trace = concolic_execution(f, args...; rands = rands)
        return val, trace
    catch err
        return err
    end
end

###
#    Iterative breath first tree search
#      - Invalidated earliest branch and use Z3 to generate an example for the
#        opposite branch
#      - explore all sides and iterate through the program to discover all branches
function fuzz(f, argtypes...)
    args = map(generate, argtypes)
    fuzz_wargs(f, args...)
end

function fuzz_wargs(f, initial_args...)
    worklist = Any[(0, initial_args, Any[])]
    tested = Any[] # did not error
    errored = Any[]

    while !isempty(worklist)
        depth, args, rands = pop!(worklist)
        trace_or_err = execute(f, args...; rands = rands)

        if !(trace_or_err isa Tuple)
            push!(errored, (args, rands, trace_or_err))
            continue
        end

        val, trace = trace_or_err
        push!(tested, (val, args, rands))

        stream = filter(trace)
        branches = Any[]
        for n in (depth+1):nbranch(stream)
            cut_stream = force_and_cut(stream, n)
            push!(branches, (n, cut_stream))
        end

        @info "Found $(length(branches)) new branches to explore"

        for (d, branch) in branches
            sat, inputs = checkStream(branch)
            if sat
                args, rands, _ = inputs
                push!(worklist, (d, args, rands))
            end
        end
    end
    tested, errored
end