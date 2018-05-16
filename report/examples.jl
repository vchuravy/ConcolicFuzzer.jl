###
# AD in 5s
###

struct D <: Number
    f::Tuple{Float64, Float64}
end
import Base: +, /, convert, promote_rule
+(x::D, y::D) = D(x.f .+ y.f)
/(x::D, y::D) = D((x.f[1]/y.f[1], (y.f[1]*x.f[2] - x.f[1]*y.f[2])/y.f[1]^2))
convert(::Type{D}, x::Real) = D((x,zero(x)))
promote_rule(::Type{D}, ::Type{<:Number}) = D

function Babylonian(x; N = 10)
    t = (1+x)/2
    for i = 2:N
        t=(t + x/t)/2
    end
    t
end
x=pi; Babylonian(D((x,1))), (sqrt(x), 0.5/sqrt(x))

##
# type-assert/type-anotations break things
## 
function Babylonian2(x::Float64; N = 10)
    t = (1+x)/2
    for i = 2:N
        t=(t + x/t)/2
    end
    t
end
x=pi; Babylonian2(D((x,1))), (sqrt(x), 0.5/sqrt(x))

##
# Let's prove something
##
using ConcolicFuzzer
import ConcolicFuzzer: assert, prove
function f3(x)
        assert(x<10)
        y = x - 10
        prove(y < 0)
        return y
    end

    sat, inputs = check(f3, 1)


function f3_2(x)
        assert(0<x<10)
        y = x - 10
        prove(y < 0)
        return y
    end

    sat, inputs = check(f3_2, 1)
###
# Fuzzing
###

    function pset_f(x)
        if x == 7
            return 100
        end
        if x*2 == x+1
            return 70
        end
        if x > 2000
            return 80
        end
        if x*2 == 1000
            return 30000
        end
        if x < 500
            return 33
        end
        if x ÷ 123 == 7
            return 1234
        end
        return 40
    end

    tested, errored = fuzz_wargs(pset_f, 2002)

    explored = collect(zip(tested...))

###
# Loops, structs, random variables
###

struct A
    x::Int
end

function g()
    x = rand(Int)
    a = A(x)

    i = 1
    while i <= a.x
        @assert i <= 10
        i +=  1
    end
    return i
end

tested, errored = fuzz_wargs(g)

explored = collect(zip(tested...))
failed = collect(zip(errored...))
