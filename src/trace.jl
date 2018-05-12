# A callsite is a function with a concolic argument set
# children are all the callsites within the function
mutable struct Callsite
    f::Any
    args::Any
    retval::Any
    depth::Int
    children::Vector{Callsite}
end

mutable struct Trace
    current::Vector{Callsite}
    stack::Vector{Vector{Callsite}}
    rands::Vector{Any}
    current_depth::Int
    Trace() = new(Callsite[], Callsite[], Any[], 0)
    Trace(rands) = new(Callsite[], Callsite[], rands, 0)
end

# Records when we enter a function and the arguments
function enter!(t::Trace, ctx, f, args...)
    vargs = map(args) do x 
        if x isa Cassette.Box
            return Cassette.meta(ctx, x)
        else
            return x
        end
    end
    t.current_depth += 1
    callsite = Callsite(f, vargs, nothing, t.current_depth, Callsite[])
    push!(t.current, callsite)
    push!(t.stack, t.current)
    t.current = callsite.children
    return nothing
end

# Records when we leave a function and the returnvalue
function exit!(t::Trace, ctx, f, retval, args...)
    vretval = if retval isa Cassette.Box
        Cassette.meta(ctx, retval)
    else
        retval
    end
    t.current = pop!(t.stack)
    t.current_depth -= 1
    last(t.current).retval = vretval
    return nothing
end

Cassette.@prehook function (f::Any)(args...) where {__CONTEXT__<:TraceCtx}
    enter!(__trace__.metadata, __trace__.context, f, args...)
end

Cassette.@posthook function (f::Any)(args...) where {__CONTEXT__<:TraceCtx}
    exit!(__trace__.metadata, __trace__.context, f, args...)
end

###
# NOTE: Ideally we would use a recursive trace generation,
#       since that would also allow us to do the tainting
#       for arbitrary functions
# 
#  Cassette.@primitive function (f::Any)(args...) where {__CONTEXT__<:TraceCtx}
#     if Cassette.is_core_primitive(__trace__, f, args...)
#         return f(args...)
#     else
#         subtrace = Any[]
#         push!(__trace__.metadata, f => subtrace)
#         new_f = Cassette.overdub(__trace__.context, f;
#                                  phase = Cassette.Transform(),
#                                  metadata = subtrace)
#         return new_f(args...)
#     end
# end
# 
# trace = Any[]
# Cassette.overdub(TraceCtx, sum; metadata = trace)(rand(3))