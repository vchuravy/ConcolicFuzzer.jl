
# A symbol is a name and the concolicly computed type
struct Sym
    name::Symbol
    _type::DataType
    Sym(base, _type::DataType) = new(Base.gensym(Symbol(base, '#', _type)), _type)
    Sym(_type::DataType) = new(Base.gensym(Symbol(_type)), _type)
end
Cassette.metadatatype(::Type{<:TraceCtx}, ::DataType) = Sym

record(args, ctx) = map(args) do arg
    if istagged(arg, ctx)
        metadata(arg, ctx)
    else
        arg
    end
end

# A callsite is a function with a concolic argument set
# children are all the callsites within the function
mutable struct Callsite
    f::Any
    args::Any
    retval::Union{Some{Any}, Nothing}
    children::Vector{Callsite}
    Callsite(f, args) = new(f, args, nothing, Callsite[])
end
Base.push!(trace::Callsite, call::Callsite) = push!(trace.children, call)

struct Metadata
    trace::Callsite
    # For current execution
    record::Vector{Sym}
    substitutes::Dict{DataType, Any}
end
Metadata() = Metadata(
    Callsite(:toplevel, ()), 
    Vector{Sym}(), 
    Dict{DataType, Vector}())

Metadata(m::Metadata, call::Callsite) = Metadata(call, m.record, m.substitutes)
Metadata(subs) = Metadata(Callsite(:toplevel, ()), Vector{Sym}(), subs)

function record!(ctx, type)
    m = ctx.metadata
    sym = Sym(:fval, type)
    push!(m.record, sym)

    if haskey(m.substitutes, type)
        subs = m.substitutes[type]
        if !isempty(subs)
            return pop!(subs), sym
        end
    end
    return nothing, sym
end
Base.push!(m::Metadata, call) = push!(m.trace, call)

function augment(record, subs)
    substitutions = Dict{DataType, Vector}()
    function insert!(type, val)
        if !haskey(substitutions, type)
            substitutions[type] = Vector{type}()
        end
        push!(substitutions[type], val)
    end

    for sym in record
        symbol = sym.name
        insert!(sym._type, subs[sym.name])
    end
    return substitutions
end

function Cassette.overdub(ctx::TraceCtx, ::typeof(rand), ::Type{T}) where T<:INTEGERS
    val, sym = record!(ctx, T)
    if val === nothing
        val = rand(T)
    end
    return tag(val::T, ctx, sym)
end

# oftype will drop tag on the x value since we are only looking at it'd type.
function Cassette.overdub(ctx::TraceCtx, ::typeof(oftype), x::Tagged, y)
    x = untag(x, ctx)
    return oftype(x, y)
end

##
# We need to manually override for IntrinsicFunctions (which are the leaf-nodes we are interested in)
# Since in tagged contexts there is an automatic fallback available.
##
function Cassette.overdub(ctx::TraceCtx{Metadata, <:Cassette.Tag}, f::Core.IntrinsicFunction, args...)
    call = Callsite(f, record(args, ctx))
    push!(ctx.metadata, call)
    retval = fallback(ctx, f, args...)
    if any(a -> istagged(a, ctx), args)
        retval = tag(retval, ctx, Sym(typeof(retval)))
    end
    call.retval = Some(istagged(retval, ctx) ? metadata(retval, ctx) : retval)
    return retval
end

##
# Recursivly trace though our program.
#
# Note: This won't trace functions that are defined primitive and there are several
#       fallbacks that Cassette provides for tagged contexts.
#
# Question: Shouldn't canoverdub for primitives be false?
##
function Cassette.overdub(ctx::TraceCtx, f, args...)
    # We need to push the callsite first into metadata
    # otherwise we run into issues with functions that throw errors
    call = Callsite(f, record(args, ctx))
    push!(ctx.metadata, call)

    # Recurse into the next function
    retval = if canrecurse(ctx, f, args...)
        newctx = similarcontext(ctx, metadata = Metadata(ctx.metadata, call))
        Cassette.recurse(newctx, f, args...)
    else
        retval = fallback(ctx, f, args...)
        # If any of our inputs was tagged we want to tag the return value so that
        # the symbolic nature of this operation is captured.
        if any(a -> istagged(a, ctx), args) && !istagged(retval, ctx)
            retval = tag(retval, ctx, Sym(typeof(retval)))
        end
        retval
    end
    call.retval = Some(istagged(retval, ctx) ? metadata(retval, ctx) : retval)
    return retval
end
