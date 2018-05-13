# Ideally we would want to use the Z3.jl interface,
# but it is currently broken.
# Ideally it looks something like this
#
# import Z3
# toZ3Type(::Type{Int64}) = Integer
# toZ3(s::Sym) = Z3.Var(toZ3Type(s._type), name = string(s.name))
# toZ3(c::T) where {T<:Real} = Z3.NumeralAst(toZ3Type(T), c)

# function symbolic(t::Trace)
#     stream = filter(t)
#     @assert isempty(t.stack)
#     @assert length(t.current) == 1
#     entry = t.current[1]

#     s = Z3.Solver()
#     vars = Dict{Sym, Any}()
#     map(entry.args) do sym
#         var = toZ3(sym)
#         vars[sym] = var
#     end

#     getZ3(s::Sym) = vars[s]
#     getZ3(c) = toZ3(c)

#     for (f, ret, args) in stream
#         z3args = map(getZ3, args)
#         if f == assert
#             @assert length(args) == 1
#             @show ret
#             Z3.solver_assert(s, z3args[1])
#         else
#             z3new = f(z3args...)
#             @assert ret isa Sym
#             vars[ret] = z3new
#         end
#     end
#     m = Z3.solver_get_model(s)
#     return s, m
# end

nbits(::Type{Int128}) = 128
nbits(::Type{Int64}) = 64
nbits(::Type{Int32}) = 32
nbits(::Type{Int16}) = 16
nbits(::Type{Int8}) = 8
nbits(::Type{UInt128}) = 128
nbits(::Type{UInt64}) = 64
nbits(::Type{UInt32}) = 32
nbits(::Type{UInt16}) = 16
nbits(::Type{UInt8}) = 8

bitsToT(::Val{128}) = UInt128
bitsToT(::Val{64}) = UInt64
bitsToT(::Val{32}) = UInt32
bitsToT(::Val{16}) = UInt16
bitsToT(::Val{8}) = UInt8
bitsToT(::Val{N}) where N = @error "Can construct type with $N bits"

toZ3(::Type{T}) where T<:Integer = "(_ BitVec $(nbits(T)))"
toZ3(::Type{Bool})    = "Bool"

toZ3(x::Integer) = "(_ bv$x $(nbits(typeof(x))))"
toZ3(x::Bool) = string(x)
toZ3(x) = @error "toZ3 for $x is not a thing yet"

FtoZ3(f::Function, ::Type{T}) where T = @error "Can't handle $f for $T yet"
FtoZ3(::typeof(Base.:-), ::Type{<:Integer}) = "bvsub"
FtoZ3(::typeof(Base.:+), ::Type{<:Integer}) = "bvadd"
FtoZ3(::typeof(Base.:*), ::Type{<:Integer}) = "bvmul"
FtoZ3(::typeof(Base.div), ::Type{<:Signed}) = "bvsdiv"
FtoZ3(::typeof(Base.div), ::Type{<:Unsigned}) = "bvudiv"
FtoZ3(::typeof(Base.:<), ::Type{<:Signed}) = "bvslt"
FtoZ3(::typeof(Base.:<), ::Type{<:Unsigned}) = "bvult"
FtoZ3(::typeof(Base.:<=), ::Type{<:Signed}) = "bvsle"
FtoZ3(::typeof(Base.:<=), ::Type{<:Unsigned}) = "bvule"
FtoZ3(::typeof(Base.:>), ::Type{<:Signed}) = "bvsgt"
FtoZ3(::typeof(Base.:>), ::Type{<:Unsigned}) = "bvugt"
FtoZ3(::typeof(Base.:>=), ::Type{<:Signed}) = "bvsge"
FtoZ3(::typeof(Base.:>=), ::Type{<:Unsigned}) = "bvuge"
#FtoZ3(::typeof(Base.:(==)), ::Type{<:Integer}) = "bveq"
#FtoZ3(::typeof(Base.:(==)), ::Type{Bool}) = "="
FtoZ3(::typeof(Base.:(==)), ::Type{<:Any}) = "="
FtoZ3(::typeof(Base.ifelse), ::Type{<:Any}) = "ite"

validName(name) = "|$(name)|"
declaration(s::Sym) = "(declare-const $(validName(s.name)) $(toZ3(s._type)))"

function symbolic(t::Trace)
    @assert isempty(t.stack)
    @assert length(t.current) == 1
    return symbolic(filter(t))
end

Tunbox(x) = typeof(x)
Tunbox(s::Sym) = s._type

function symbolic(stream)
    declarations = IOBuffer()
    model = IOBuffer()

    function declare(s::Sym)
        decl = declaration(s)
        println(declarations, decl)
        return validName(s.name)
    end

    vars = Dict{Sym, String}()

    function getZ3(s::Sym)
        if !haskey(vars, s)
            vars[s] = declare(s)
        end
        vars[s]
    end
    getZ3(c) = toZ3(c)

    for (f, ret, args) in stream
        z3args = join(map(getZ3, args), " ")
        if f == assert || f == prove
            @assert length(args) == 1
            @assert ret isa Bool
            z3ret = toZ3(ret)
            stmt = "(= $z3args $(z3ret))"
            if f == prove
                stmt = "(not $stmt)"
            end
            stmt = "(assert $stmt)"
        else
            @assert ret isa Sym
            # HACK!
            T = reduce(promote_type, map(Tunbox, args))
            z3f = FtoZ3(f, T)
            z3ret = getZ3(ret)
            stmt = "(assert (= $z3ret ($z3f $z3args)))"
        end
        println(model, stmt)
    end
    seekstart(model)
    write(declarations, model)
    seekstart(declarations)
    declarations
end

function runZ3(model)
    tinput = Pipe()
    output = Pipe()
    run(pipeline(`z3 -smt2 -in`, stdin=tinput, stdout=output), wait=false)
    input = IOBuffer()
    println(input, "(set-option :pp.bv-literals false)")
    write(input, model)
    write(input, "(check-sat)\n")
    write(input, "(get-model)\n")
    seekstart(input)
    @debug begin
        z3input = read(input, String)
        seekstart(input)
        "Z3 input" model=z3input
    end
    write(tinput, input)
    close(tinput)
    close(output.in)
    sat = readline(output)
    model = read(output, String)
    @debug "Z3 output" sat model
    return (sat == "sat", model)
end

function fromz3type(typ)
    if typ == "Int"
        return Int
    elseif typ == "Bool"
        return Bool
    else
        r_typ = r"\(_ BitVec (\d{1,3})\)"
        m = match(r_typ, typ)
        if m === nothing
            @error "What even is $typ"
        else
            return bitsToT(Val(parse(Int, m.captures[1])))
        end
    end
end

function fromz3val(T, val)
    if T == Int
        return parse(Int, val)
    elseif T == Bool
        return parse(Bool, val)
    else
        return parse(T, split(val)[2][3:end])
    end
end

function stringToType(_type)
    if _type == "Int128"
        return Int128
    elseif _type == "Int64"
        return Int64
    elseif _type == "Int32"
        return Int32
    elseif _type == "Int16"
        return Int16
    elseif _type == "Int8"
        return Int8
    elseif _type == "UInt128"
        return UInt128
    elseif _type == "UInt64"
        return UInt64
    elseif _type == "UInt32"
        return UInt32
    elseif _type == "UInt16"
        return UInt16
    elseif _type == "UInt8"
        return UInt8
    elseif _type == "Bool"
        return Bool
    end
end

# This is really hacky, in reality we would want to properly parse
# s-expr.
function parseZ3(model)
    lines = split(chomp(model), '\n')[2:end-1]
    @assert length(lines) % 2 == 0
    inputs = Any[]

    r_def = r"define-fun\s+(\|.*\|)\s+\(\)\s+(\(.+?\)|Bool|Int)\s+(\(.+?\)|\S+)"
    for i in 1:2:length(lines)
        def = strip(join(lines[i:i+1]))[2:end-1]
        m = match(r_def, def)
        if m === nothing
            @error "Regex didn't match: $def"
        end
        name = m.captures[1]
        T = fromz3type(m.captures[2])
        val = fromz3val(T, m.captures[3])
        push!(inputs, (name, val))
    end

    args = Any[]
    rands = Any[]
    others = Any[]

    r_arg = r"\|##arg_(\d+)#(\w+)#\d+\|"
    r_rand = r"\|##rand#(\w+)#(\d+)\|"
    r_others = r"\|##(\w+)#\d+\|"
    for (name, val) in inputs
        m = match(r_arg, name)
        if m !== nothing
            id = parse(Int, m.captures[1])
            T = stringToType(m.captures[2])
            if T <: Integer
                val = val % T
            end
            push!(args, (id, val))
            continue
        end
        m = match(r_rand, name)
        if m !== nothing
            id = parse(Int, m.captures[2])
            T = stringToType(m.captures[1])
            if T <: Integer
                val = val % T
            end
            push!(rands, (id, val))
            continue
        end
        m = match(r_others, name)
        if m !== nothing
            T = stringToType(m.captures[1])
            if T <: Integer
                val = val % T
            end
            push!(others, (name, val))
            continue
        end
        @error "Can't parse $name"
    end
    args = Tuple(map(x -> x[2], sort(args))) # sort by id
    rands = map(x -> x[2], sort(rands)) # sort by id
    args, rands, others
end