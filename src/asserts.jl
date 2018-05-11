assert(x::Bool) = x

Cassette.@primitive function assert(x::@Box) where {__CONTEXT__<:TraceCtx}
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