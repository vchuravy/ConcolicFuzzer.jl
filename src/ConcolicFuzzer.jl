module ConcolicFuzzer

export execute, check, fuzz, fuzz_wargs, fuzz_and_check

# Cassette is a non-standard execution engine for Julia
# It allows for contextualised execution. I use Cassette to generate
# concolic traces of arbitrary Julia programs. Each execution creates
# a particular trace depending on the concrete input arguments.
using Cassette
using Cassette: Tagged, tag, untag, istagged, metadata, hasmetadata,
                enabletagging, overdub, canrecurse, similarcontext, fallback

Cassette.@context TraceCtx

anything(x) = x
anything(x::Some) = something(x)

include("taint.jl")
include("trace.jl")
include("asserts.jl")
include("traceutils.jl")

"""
    execute(f, x)

Executes the function `f` concolicly by tainting the argument `x`.
Returns a tuple with the first element being the concrete value,
the second element a boolean that indicates whether the output is dependend on the input
and the third element is a concolic Trace.
"""
function execute(f, args...; rands = Any[])
    trace = Callsite[]
    ctx = enabletagging(TraceCtx(metadata = trace, pass = InsertAssertsPass), f)
    tagged_args = map(enumerate(args)) do (i, arg)
        sym = Sym(Symbol(:arg_, i), typeof(arg))
        tag(arg, ctx, sym)
    end
    y = try
        Cassette.@overdub(ctx, f(tagged_args...))
    catch err
        err
    end

    # Unpack the trace
    @assert length(trace) == 1
    trace = trace[1]
    # @assert length(trace.children) == 1
    # trace = first(trace.children) 
    verify(trace)

    if istagged(y, ctx)
        vy = untag(y, ctx)
    else
        vy = y
    end

    symb = istagged(y, ctx) && hasmetadata(y, ctx)
    return (vy, symb, trace)
end

include("z3.jl")
include("fuzzer.jl")

"""
    check(f, args...)

Given a `f` that uses manually inserted `assert` and `prove` statements.
Check if the symbolic part of the trace is satisfiable or not.
"""
function check(f, args...; rands = Any[])
    _, _, trace = execute(f, args...; rands = rands)
    stream = filter(trace)
    return checkStream(stream)
end

"""
    fuzz_and_check(f, argtypes...)

Ussing a user provided `prove` stament, proves that
the condition holds across all reachable branches.

Returns a list of `(sat, args)` where sat indicates
the trace was satisfiable and under which arguments.
To prove a statement you want to have branches be
unsatisfiable.

NOTE:
  - Do not use manually inserted `assert` statements, since
    that will throw `fuzz` off the trail. You can use `@assert`
    to the same effect.
"""
function fuzz_and_check(f, argtypes...)
    tested, errored = fuzz(f, argtypes...)
    ntested = Any[]
    for (out, args, rands) in tested
        result = check(f, args...; rands=rands)
        push!(ntested, result)
    end
    return ntested
end
end # module
