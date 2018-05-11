# A symbol is a name and the concolicly computed type
struct Sym
    name::Symbol
    _type::DataType
end
Cassette.metatype(::Type{<:TraceCtx}, ::DataType) = Sym

##
# NOTE: For now do an explicit annotation of the leave nodes, once recursive trace generation work 
#       one can use that for tainting
# const LEAF_FUNCTIONS = [
#     (Core.Intrinsics.slt_int,2),
#     (Core.Intrinsics.add_int,2),
# ]
const LEAF_FUNCTIONS = [
    (Base.:-, 2),
    (Base.:+, 2),
    (Base.:*, 2),
    (Base.div, 2),
    (Base.:<, 2),
    (Base.:<=, 2),
    (Base.:>, 2),
    (Base.:>=, 2),
    (Base.:(==), 2),
]

for (f, arity) in LEAF_FUNCTIONS
    if arity == 1
        @eval begin
            Cassette.@primitive function (::typeof($f))(x::@Box) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vv = $f(vx)
                sv = Sym(Base.gensym(), typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
        end
    elseif arity == 2
        @eval begin
            Cassette.@primitive function (::typeof($f))(x::@Box, y::@Box) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                vv = $f(vx, vy)
                sv = Sym(Base.gensym(), typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(x::@Box, vy) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vv = $f(vx, vy)
                sv = Sym(Base.gensym(), typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(vx, y::@Box) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                vv = $f(vx, vy)
                sv = Sym(Base.gensym(), typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
        end
    end
end

###
# Tainting of values coming from random number generators
###

Cassette.@primitive function rand(::Type{Int64}) where {__CONTEXT__<:TraceCtx}
    resevoir = __trace__.metadata.rands
    if length(resevoir) >= 1
        vv = pop!(resevoir)
        @assert vv isa Int64
    else 
        vv = rand(Int64)
    end
    sv = Sym(Base.gensym(:rand), typeof(vv))
    return Cassette.Box(__trace__.context, vv, sv)
end