
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

nodub(f, args...) = Expr(:call, Expr(:nooverdub, f), args...)

# Define a Cassette pass to insert asserts after branches
function insertasserts(ctx, ref)
    ir = ref.code_info
    locations = Int[]
    Cassette.insert_statements!(ir.code, ir.codelocs,
        (stmt, i) -> Base.Meta.isexpr(stmt, :gotoifnot) ? 2 : nothing, 
        (stmt, i) -> [
            Expr(:call, ConcolicFuzzer.assert, stmt.args[1]),
            stmt
        ])

    # Taint foreigncalls
    # TODO: llvmcall, check if stmts.args[2] supported
    # This works but is way to aggressive.
    #=
    Cassette.insert_statements!(ir.code, ir.codelocs,
        (stmt, i) -> begin
            stmt = Base.Meta.isexpr(stmt, :(=)) ? stmt.args[2] : stmt
            if Base.Meta.isexpr(stmt, :foreigncall) && supported(stmt.args[2])
                12
            else
                nothing
            end
        end,
        (stmt, i) -> begin
            if Base.Meta.isexpr(stmt, :(=))
                tagstmt = Expr(:(=), stmt.args[1])
                stmt = stmt.args[2]
            else
                tagstmt = nothing
            end
            # setup slot for if-else
            slot = Core.SlotNumber(length(ir.slotflags) + 1)
            push!(ir.slotflags, 0x10) # TODO check flag value
            push!(ir.slotnames, gensym(:temp))
            # obtain location as stacktrace
            type = stmt.args[2]

            # Helper to more easily create result
            result = Any[]
            insert!(stmt) = (id = i+length(result); push!(result, stmt); Core.SSAValue(id))

            #=
            stack = StackTraces.stacktrace()
            loc = StackTraces.remove_frames!(stack, :execute)
            val, sym = record!(ctx, loc, type)
            if val === nothing
                val = stmt
            end
            return tag(val, ctx, sym)
            =#
            stack  = insert!(nodub(StackTraces.stacktrace))
            loc    = insert!(nodub(StackTraces.remove_frames!, stack, QuoteNode(:execute)))
            record = insert!(nodub(ConcolicFuzzer.record!, Expr(:contextslot), loc, type))
            val    = insert!(nodub(Base.getindex, record, 1))
            sym    = insert!(nodub(Base.getindex, record, 2))
            cond   = insert!(nodub(Core.:(===), val, nothing))
            ifstmt = insert!(Expr(:gotoifnot, cond, #=fill in later=#))
            bb1    = insert!(Expr(:(=), slot, stmt))
            elstmt = insert!(Expr(:goto, #=fill in later=#))
            bb2    = insert!(Expr(:(=), slot, val))
            tag    = insert!(nodub(Cassette.tag, slot , Expr(:contextslot), sym))

            # fixup if and else
            push!(result[ifstmt.id - i + 1].args, bb2.id)
            result[elstmt.id - i + 1] = Core.GotoNode(tag.id)

            if tagstmt === nothing
                push!(result, tag)
            else
                push!(tagstmt.args, tag)
                push!(result, tagstmt)
            end
            return result
        end)
    =#
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