module ConcolicFuzzer

export concolic_execution, check, fuzz, fuzz_wargs, fuzz_and_check

# Cassette is a non-standard execution engine for Julia
# It allows for contextualised execution. I use Cassette to generate
# concolic traces of arbitrary Julia programs. Each execution creates
# a particular trace depending on the concrete input arguments.
import Cassette
Cassette.@context TraceCtx

include("trace.jl")
include("taint.jl")
include("asserts.jl")
include("traceutils.jl")

"""
    concolic_execution(f, x)

Executes the function `f` concolicly by tainting the argument `x`.
Returns a tuple with the first element being the concrete value,
the second element a boolean that indicates whether the output is dependend on the input
and the third element is a concolic Trace.
"""
function concolic_execution(f, args...; rands = Any[])
    ctx = TraceCtx(f) 
    trace = Trace(rands)
    vals = map(enumerate(args)) do (i, arg)
        Cassette.Box(ctx, arg, Sym(Symbol(:arg_, i), typeof(arg)))
    end
    over_f = Cassette.overdub(ctx, f,
                         metadata = trace,
                         pass = InsertAssertsPass,
                         boxes=Val(true))
    y = nothing
    try
        y = over_f(vals...)
    catch err
        y = err
        while trace.current_depth != 0
            unwind!(trace, err)
        end
    end
    @assert isempty(trace.stack)
    verify(trace)
    if Cassette.isboxed(ctx, y)
        vy = Cassette.unbox(ctx, y)
    else
        vy = y
    end
    symb = Cassette.isboxed(ctx, y) && Cassette.meta(ctx, y) != Cassette.unused
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
    _, _, trace = concolic_execution(f, args...; rands = rands)
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
