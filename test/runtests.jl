using ConcolicFuzzer
using Test 

import ConcolicFuzzer: assert, prove

@testset "Simple tests" begin

    function f2(x)
        b = x < 10
        y = x - 10
        c = y < 0
        return y
    end

    val, symb, trace = execute(f2, 1);

    @test val == -9
    @test symb == true
    @test length(ConcolicFuzzer.flatten(trace)) == 3

    sanity_f1(x) = x * 2
    sanity_f2(x) = x ÷ 2
    sanity_f3(x) = (x ÷ 2) * 4 + 3
    
    val, symb, trace = execute(sanity_f1, 10)
    @test val == 20
    @test symb

    val, symb, trace = execute(sanity_f2, 10)
    @test val == 5
    @test symb

    val, symb, trace = execute(sanity_f3, 10)
    @test val == 23
    @test symb
end

@testset "Check" begin
    function f3(x)
        assert(x<10)
        y = x - 10
        prove(y < 0)
        return y
    end

    sat, inputs = check(f3, 1)
    # Underflow possible at -9223372036854775808
    @test sat == true

    function f4(x)
        assert(0<x<10)
        y = x - 10
        prove(y < 0)
        return y
    end

    # any input works as long as we don't need to hit any branches
    # if you have branches use `fuzz_and_check`
    sat, inputs = check(f4, 1)
    @test sat == false
end


@testset "Branches" begin
    function f(x::Int)
        @assert x < 10
        y = x - 10
        @assert y < 0
        return y
    end

    val, symb, trace = execute(f, 1);

    @test val == -9
    @test symb == true
    @test length(ConcolicFuzzer.flatten(trace)) == 5

    function g(x)
        if x < 10
            return 12
        else
            return x + 2
        end
    end

    val, symb, trace = execute(g, 1);

    @test val == 12
    @test symb == false

    val, symb, trace = execute(g, 10);

    @test val == 12
    @test symb == true
end

@testset "Fuzzing!" begin
    # Examples from the PSet
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

    outs = explored[1]
    args = explored[2]
    rands = explored[3]

    @test length(tested) == 7
    @test (7,) in args
    @test (1,) in args
    @test (500,) in args

    @test 100 in outs
    @test 70 in outs
    @test 80 in outs
    @test 30000 in outs
    @test 33 in outs
    @test 1234 in outs
    @test 40 in outs
end

@testset "Fuzzing over an abstract type" begin
    function pure_madness(x::T) where T
        if x < typemax(T)
            return 42
        end
        return 9001
    end

    tested, errored = fuzz(pure_madness, Integer)

    @test length(tested) == 21

    tested, errored = fuzz(pure_madness, Union{Int32, UInt64})
    @test length(tested) == 4
end

@testset "Randomness" begin
    function r1()
        return rand(Int)
    end
    val, symb, trace, record = execute(r1);
    @test symb == true

    function r2()
        x = rand(Int)
        if x < 10
            return 1337
        else
            return 42
        end
    end

    val, symb, trace, record = execute(r2);

    subs = Dict(Int64 => Int64[1])
    val, symb, trace, record = execute(r2, subs=subs);
    @test val == 1337

    subs = Dict(Int64 => Int64[12])
    val, symb, trace, record = execute(r2, subs = subs);
    @test val == 42

    function r3()
        x = rand(Int)
        y = rand(Int)

        if x + y < 10
            return 42
        end
        return 12
    end
    val, symb, trace, record = execute(r3);

    subs = Dict(Int64 => Int64[1, 2])
    val, symb, trace, record = execute(r3, subs = subs);
    @test val == 42

    subs = Dict(Int64 => Int64[6, 7])
    val, symb, trace, record = execute(r3, subs = subs);
    @test val == 12

    tested, errored = fuzz(r3)
end

@testset "Simple Loops" begin
    function hh0(x)
        acc = 0
        i = 1
        while i <= 10
            i += 1
            acc += x
        end
        acc
    end
    val, symb, trace = execute(hh0, 1);
    @test val == 10
    @test symb == true
    @test length(ConcolicFuzzer.filter(trace)) == 10

    function hh1(x)
        acc = 0
        i = 1
        while i <= x
            acc += 1
            i += 1
        end
        acc
    end

    val, symb, trace = execute(hh1, 10);
    @test val == 10
    @test symb == false
    @test length(ConcolicFuzzer.filter(trace)) == 22 
end

@testset "Fuzzing of loops" begin
    # Simulate out_of_bounds
    function out_of_bounds(N)
        i = 1
        while i <= N
            @assert i <= 10
            i +=  1
        end
        return i
    end

    tested, errored = fuzz_wargs(out_of_bounds, 0)

    explored = collect(zip(tested...))
    outs = explored[1]
    args = explored[2]
    rands = explored[3]

    for i in 0:10
        @test (i,) in args
    end

    failed = collect(zip(errored...))
    outs = failed[1]
    args = failed[2]
    rands = failed[3]

    @test length(outs) >= 1
    @test first(outs) isa AssertionError
end

struct A
    x::Int
end
@testset "Structs" begin
    function propagate(x)
        a = A(x)
        return a.x
    end
    val, symb, trace = execute(propagate, 10);
    @test val == 10
    @test symb == true

    range() = 1:10
    val, symb, trace = execute(range);
    @test symb == false
end

@testset "Arrays" begin
    function store_and_read(x, i, j)
        A = Array{Int}(undef, 10)
        A[i] = x
        x = 0 # Destroy symbol character of x
        return A[j]
    end
    val, symb, trace = execute((x)->store_and_read(x, 5, 5), 1);
    @test val == 1
    @test symb == true

    val, symb, trace = execute((x)->store_and_read(x, 1, 7), 1);
    @test symb == false
end

@testset "Complex Loops" begin
    function h0()
        acc = 0
        for i in 1:10
            acc += 1
        end
        return acc
    end

    val, symb, trace = execute(h0);
    @test val == 10
    @test symb == false

    function h1(x)
        acc = 0
        for i in 1:10
            acc += x
        end
        return acc
    end

    val, symb, trace = execute(h1, 1);
    @test val == 10
    @test symb == true
    @test length(ConcolicFuzzer.filter(trace)) == 10

    function h2(N)
        acc = 0
        for i in 1:N
            acc += 1
        end
        return acc
    end

    val, symb, trace = execute(h2, 10);
    @test val == 10
    @test symb == false
    @test_broken length(ConcolicFuzzer.filter(trace)) == 25

    function h3(N)
        acc = 0
        for i in 1:N
            acc += i
        end
        return acc
    end

    val, symb, trace = execute(h3, 10);
    @test val == 55 
    @test symb == true
end

# @testset "Fuzz supported datatypes" begin
#    function over_dt(::Type{T}) where T
#       if T == Int64
#         return true
#       else
#         return false
#       end
#     end

#     tested, errored = fuzz((x)->over_dt(ConcolicFuzzer.enumerateSupportedTypes(x)), Int)
#     @test length(tested) == 11

#     function over_dt2(::Type{Int8})
#         return false
#     end

#     function over_dt2(::Type{Int64})
#         return true
#     end

#     tested, errored = fuzz((x)->over_dt2(ConcolicFuzzer.enumerateSupportedTypes(x)), Int)
#     @test length(tested) == 2
#     @test length(errored) == 9
# end

@testset "Fuzz and Check" begin
    function fc(y)
        @assert(0 < y)
        if y < 10
            x = y - 5
        else
            x = y - 7
        end
        ConcolicFuzzer.prove(x < y)
    end
    result = ConcolicFuzzer.fuzz_and_check(fc, Int)
    @test any(map(r->r[1], result)) == false
end

# @testset "Complicated Fuzzing" begin
#     function mysum(A, N)
#         acc = 0
#         for i in 1:N
#             acc += A[i]
#         end
#         return acc
#     end

#     fuzz_wargs((N)->mysum(ones(10),N), 1)

#     function mysum_inbounds(A, N)
#         @assert N <= length(A)
#         acc = 0
#         @inbounds for i in 1:N
#             acc += A[i]
#         end
#         return acc
#     end

#     fuzz_wargs((N)->mysum_inbounds(ones(10),N), 1)
# end

