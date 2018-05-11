module ConcolicFuzzer

export concolic_execution, fuzz, fuzz_wargs

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
        Cassette.Box(ctx, arg, Sym(Base.gensym(Symbol(:arg_, i)), typeof(arg)))
    end
    over_f = Cassette.overdub(ctx, f,
                         metadata = trace,
                         pass = InsertAssertsPass,
                         boxes=Val(true))
    y = over_f(vals...)
    @assert isempty(trace.stack)
    verify(trace)
    if Cassette.isboxed(ctx, y)
        return (Cassette.unbox(ctx, y), true, trace)
    else
        return (y, false, trace)
    end
end

include("z3.jl")
include("fuzzer.jl")

end # module
