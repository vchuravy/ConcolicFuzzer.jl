
"""
    assert(x::Bool)

Assert that the condition generating `x` holds true.
Returns `x`

"""
assert(x::Bool) = x 
Cassette.@primitive function assert(x::@Box) where {__CONTEXT__<:TraceCtx}
    ctx = __trace__.context
    return Cassette.unbox(ctx, x)
end


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
Cassette.@primitive function prove(x::@Box) where {__CONTEXT__<:TraceCtx}
    ctx = __trace__.context
    return Cassette.unbox(ctx, x)
end

# Define a Cassette pass to insert asserts after branches
function insertasserts(@nospecialize(signature), method_body)
    code = method_body.code
    new_code = Any[]
    for stmnt in code
        Cassette.replace_match!(x-> Base.Meta.isexpr(x, :gotoifnot), stmnt) do goto
            arg = goto.args[1]
            assert_stmnt = :($assert($arg))
            push!(new_code, assert_stmnt)
        end
        push!(new_code, stmnt)
    end
    method_body.code = new_code
    return method_body
end

const InsertAssertsPass = Cassette.@pass(insertasserts)