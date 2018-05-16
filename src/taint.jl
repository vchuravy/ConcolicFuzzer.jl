# A symbol is a name and the concolicly computed type
struct Sym
    name::Symbol
    _type::DataType
    Sym(base, _type::DataType) = new(Base.gensym(Symbol(base, '#', _type)), _type)
    Sym(_type::DataType) = new(Base.gensym(Symbol(_type)), _type)
end
Cassette.metatype(::Type{<:TraceCtx}, ::DataType) = Sym

# Base.print(io, s::Sym) = print(io, s.name)

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
    (Base.ifelse, 3),
]

for (f, arity) in LEAF_FUNCTIONS
    if arity == 1
        @eval begin
            Cassette.@primitive function (::typeof($f))(x::@Box(Any, Sym)) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vv = $f(vx)
                sv = sx == Cassette.unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
        end
    elseif arity == 2
        @eval begin
            Cassette.@primitive function (::typeof($f))(x::@Box(Any, Sym), y::@Box(Any, Sym)) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                both_unused = sx == Cassette.unused && sy == Cassette.unused
                vv = $f(vx, vy)
                sv = both_unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(x::@Box(Any, Sym), vy) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vv = $f(vx, vy)
                sv = sx == Cassette.unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(vx, y::@Box(Any, Sym)) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                vv = $f(vx, vy)
                sv = sy == Cassette.unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
        end
    elseif arity == 3
        @eval begin
            Cassette.@primitive function (::typeof($f))(x::@Box(Any, Sym), y::@Box(Any, Sym), z::@Box(Any, Sym)) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                vz, sz = Cassette.unbox(ctx, z), Cassette.meta(ctx, z)
                unused = sx == Cassette.unused && sy == Cassette.unused && sz == Cassette.unused
                vv = $f(vx, vy, vz)
                sv = unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(x::@Box(Any, Sym), y::@Box(Any, Sym), vz) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                unused = sx == Cassette.unused && sy == Cassette.unused
                vv = $f(vx, vy, vz)
                sv = unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(x::@Box(Any, Sym), vy, z::@Box(Any, Sym)) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vz, sz = Cassette.unbox(ctx, z), Cassette.meta(ctx, z)
                unused = sx == Cassette.unused && sz == Cassette.unused
                vv = $f(vx, vy, vz)
                sv = unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(vx, y::@Box(Any, Sym), z::@Box(Any, Sym)) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                vz, sz = Cassette.unbox(ctx, z), Cassette.meta(ctx, z)
                unused = sy == Cassette.unused && sz == Cassette.unused
                vv = $f(vx, vy, vz)
                sv = unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(x::@Box(Any, Sym), vy, vz) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vx, sx = Cassette.unbox(ctx, x), Cassette.meta(ctx, x)
                vv = $f(vx, vy, vz)
                sv = sx == Cassette.unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(vx, y::@Box(Any, Sym), vz) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vy, sy = Cassette.unbox(ctx, y), Cassette.meta(ctx, y)
                vv = $f(vx, vy, vz)
                sv = sy == Cassette.unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
            Cassette.@primitive function (::typeof($f))(vx, vy, z::@Box(Any, Sym)) where {__CONTEXT__<:TraceCtx}
                ctx = __trace__.context
                vz, sz = Cassette.unbox(ctx, z), Cassette.meta(ctx, z)
                vv = $f(vx, vy, vz)
                sv = sz == Cassette.unused ? Cassette.unused : Sym(typeof(vv))
                return Cassette.Box(ctx, vv, sv)
            end
        end
    end
end

###
# Tainting of values coming from random number generators
###

Cassette.@primitive function rand(::Type{T}) where {T <: Integer, __CONTEXT__<:TraceCtx}
    resevoir = __trace__.metadata.rands
    if length(resevoir) >= 1
        vv = pop!(resevoir)::T
    else 
        vv = rand(T)
    end
    sv = Sym(:rand, typeof(vv))
    return Cassette.Box(__trace__.context, vv, sv)
end