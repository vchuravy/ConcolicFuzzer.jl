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

toZ3(::Type{Int64}) = "Int" # TODO use BitVectors
toZ3(::Type{Bool}) = "Bool"

toZ3(x) = string(x)

toZ3(f::Function) = @error "Can't handle $f yet"
toZ3(::typeof(Base.:-)) = "-"
toZ3(::typeof(Base.:+)) = "+"
toZ3(::typeof(Base.:*)) = "*"
toZ3(::typeof(Base.div)) = "div"
toZ3(::typeof(Base.:<)) = "<"
toZ3(::typeof(Base.:<=)) = "<="
toZ3(::typeof(Base.:>)) = ">"
toZ3(::typeof(Base.:>=)) = ">="
toZ3(::typeof(Base.:(==))) = "="

validName(name) = "|$(name)|"
declaration(s::Sym) = "(declare-const $(validName(s.name)) $(toZ3(s._type)))"

function symbolic(t::Trace)
    @assert isempty(t.stack)
    @assert length(t.current) == 1
    return symbolic(filter(t))
end

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
            z3f = toZ3(f)
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
    input = Pipe()
    output = Pipe()
    run(pipeline(`z3 -smt2 -in`, stdin=input, stdout=output), wait=false)
    write(input, model)
    write(input, "(check-sat)\n")
    write(input, "(get-model)\n")
    close(input)
    close(output.in)
    sat = readline(output)
    model = read(output, String)
    return (sat == "sat", model)
end

function fromz3type(typ)
    if typ == "Int"
        return Int
    elseif typ == "Bool"
        return Bool
    else
        @error "What even is $typ"
    end
end

# This is really hacky, in reality we would want to properly parse
# s-expr.
function parseZ3(model)
    lines = split(chomp(model), '\n')[2:end-1]
    @assert length(lines) % 2 == 0
    inputs = Any[]
    for i in 1:2:length(lines)
        def = strip(join(lines[i:i+1]))[2:end-1]
        atoms = split(def)
        @assert atoms[1] == "define-fun"
        name = atoms[2]
        @assert atoms[3] == "()"
        T = fromz3type(atoms[4])
        val = parse(T, atoms[5])
        push!(inputs, (name, val))
    end

    args = Any[]
    rands = Any[]
    others = Any[]

    r_arg = r"\|##arg_(\d+)#\d+\|"
    r_rand = r"\|##rand#(\d+)\|"
    for (name, val) in inputs
        m = match(r_arg, name)
        if m !== nothing
            id = parse(Int, first(m.captures))
            push!(args, (id, val))
            continue
        end
        m = match(r_rand, name)
        if m !== nothing
            id = parse(Int, first(m.captures))
            push!(rands, (id, val))
            continue
        end
        push!(others, (name, val))
    end
    args = Tuple(map(x -> x[2], sort(args))) # sort by id
    rands = map(x -> x[2], sort(rands)) # sort by id
    args, rands, others
end