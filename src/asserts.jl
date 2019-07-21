
"""
    assert(x::Bool)

Assert that the condition generating `x` holds true.
Returns `x`

"""
assert(x::Bool) = x 

"""
    prove(x::Bool)

```julia
assert(x < 10)
y = x - 10
prove(y < 0)
```

Will turn into the corresponding SMT2 program:

```
(declare-const x Int)
(declare-const y Int)
(assert (< x 10))
(assert (= y (- x 10)))
(assert (not (< y 0)))
(check-sat)
```

If the model is not satisfiable, given the pre-condition defined by `assert`
the post-condition given by `prove` holds.

For more information see `check`.
"""
prove(x::Bool) = x

# Define a Cassette pass to insert asserts after branches
function insertasserts(ctx, ref)
    ir = ref.code_info
    locations = Int[]
    Cassette.insert_statements!(ir.code, ir.codelocs,
        (stmt, i) -> Base.Meta.isexpr(stmt, :gotoifnot) ? 2 : nothing, 
        (stmt, i) -> [
            Expr(:call, Expr(:nooverdub, GlobalRef(ConcolicFuzzer, :assert)), stmt.args[1]),
            stmt
        ])

    # Taint foreigncalls
    # TODO: llvmcall
    Cassette.insert_statements!(ir.code, ir.codelocs,
        (stmt, i) -> begin
            stmt = Base.Meta.isexpr(stmt, :(=) ? stmt.args[2] : stmt)
            Base.Meta.isexpr(stmt, :foreigncall) ? 4 : nothing
        end
        (stmt, i) -> begin
            typestmt = Expr(:call, Expr(:nooverdub, GlobalRef(Core, :typeof)), Core.SSAValue(i))
            symstmt = Expr(:call, Expr(:nooverdub, GlobalRef(ConcolicFuzzer, :Sym)), :fval, Core.SSAValue(i+1))
            tagstmt = Expr(:call, Expr(:nooverdub, GlobalRef(Cassette, :tag), Core.SSAValue(i), Expr(:contextslot), Core.SSAValue(i+2)))

            if Base.Meta.isexpr(stmt, :(=))
                tagstmt = Expr(:(=), stmt.args[1], tagstmt)
                stmt = stmt.args[2]
            end
            [stmt, typestmt, symstmt, tagstmt]
        end)
    ir.ssavaluetypes = length(ir.code)
    return ir
end

const InsertAssertsPass = Cassette.@pass insertasserts

# We can't use primitives since otherwise our tracer won't trace assert and prove statements 
# Which is the entire point.
function Cassette.overdub(ctx::TraceCtx, f::F, x::Tagged) where F <: Union{Core.typeof(assert), Core.typeof(prove)}
    call = Callsite(f, record((x, ), ctx))
    retval = untag(x, ctx)
    call.retval = Some(retval)
    push!(ctx.metadata, call)
    return retval 
end