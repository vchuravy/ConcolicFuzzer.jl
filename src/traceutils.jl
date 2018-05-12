function recurse(f, call)
    f(call)
    map(call.children) do child
        recurse(f, child)
    end
end

"""
    flatten(t::Trace)

Helper function that flattens a trace generated by `concolic_execution` so that only the leaf nodes are present.
"""
function flatten(t::Trace)
    stream = Tuple{Any, Any, Tuple}[]
    @assert isempty(t.stack)
    @assert length(t.current) == 1
    recurse(t.current[1]) do call
        if isempty(call.children)
            push!(stream, (call.f, call.retval, call.args))
        end
    end
    return stream
end

function filter(t::Trace)
    stream = Tuple{Any, Any, Tuple}[]
    @assert isempty(t.stack)
    @assert length(t.current) == 1
    recurse(t.current[1]) do call
        if isempty(call.children) && any(a->isa(a,Sym), call.args)
            push!(stream, (call.f, call.retval, call.args))
        end
    end
    return stream
end


"""
    verify(trace, merciless=false)

Use `verify(trace, true)` to see built-ins that cause concrete execution
"""
function verify(t::Trace, merciless=false)
    @assert isempty(t.stack)
    @assert length(t.current) == 1
    recurse(t.current[1]) do call
        if any(a->isa(a, Sym), call.args) && !(call.retval isa Sym)
            if typeof(call.f) <: Core.Builtin && !merciless
                return
            end
            if call.f == assert || call.f == prove
                return
            end
            # Not sure why these occur
            if call.retval isa Cassette.Unused
                return
            end
            @warn "Function $(call.f) did not propagate taint, $((call.retval, call.args))"
        end
    end
    return nothing
end
