###
# Tainting of values coming from random number generators
###

# Cassette.@primitive function rand(::Type{T}) where {T <: Integer, __CONTEXT__<:TraceCtx}
#     resevoir = __trace__.metadata.rands
#     if length(resevoir) >= 1
#         vv = pop!(resevoir)::T
#     else 
#         vv = rand(T)
#     end
#     sv = Sym(:rand, typeof(vv))
#     return Cassette.Box(__trace__.context, vv, sv)
# end