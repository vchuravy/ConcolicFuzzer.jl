using ConcolicFuzzer
using Test 

import ConcolicFuzzer: assert

@testset "Simple tests" begin
    function f(x::Int)
        @assert x < 10
        y = x - 10
        @assert y < 0
        return y
    end

    val, symb, trace = concolic_execution(f, 1);

    @test val == -9
    @test symb == true
    @test length(ConcolicFuzzer.flatten(trace)) == 5

    function f2(x)
        b = x < 10
        y = x - 10
        c = y < 0
        return y
    end

    val, symb, trace = concolic_execution(f2, 1);

    @test val == -9
    @test symb == true
    @test length(ConcolicFuzzer.flatten(trace)) == 3

    function f3(x)
        assert(x<10)
        y = x - 10
        assert(y < 0)
        return y
    end

    val, symb, trace = concolic_execution(f3, 1);

    @test val == -9
    @test symb == true
    @test length(ConcolicFuzzer.flatten(trace)) ==5 


    sanity_f1(x) = x * 2
    sanity_f2(x) = x ÷ 2
    sanity_f3(x) = (x ÷ 2) * 4 + 3
    
    val, symb, trace = concolic_execution(sanity_f1, 10)
    @test val == 20
    @test symb

    val, symb, trace = concolic_execution(sanity_f2, 10)
    @test val == 5
    @test symb

    val, symb, trace = concolic_execution(sanity_f3, 10)
    @test val == 23
    @test symb
end

@testset "Branches" begin
    function g(x)
        if x < 10
            return 12
        else
            return x + 2
        end
    end

    val, symb, trace = concolic_execution(g, 1);

    @test val == 12
    @test symb == false

    val, symb, trace = concolic_execution(g, 10);

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

@testset "Randomness" begin
    function r1()
        return rand(Int)
    end
    val, symb, trace = concolic_execution(r1);
    @test symb == true

    function r2()
        x = rand(Int)
        if x < 10
            return 1337
        else
            return 42
        end
    end

    val, symb, trace = concolic_execution(r2, rands = [9]);
    @test val == 1337

    val, symb, trace = concolic_execution(r2, rands = [12]);
    @test val == 42

    function r3()
        x = rand(Int)
        y = rand(Int)

        if x + y < 10
            return 42
        end
        return 12
    end

end

# @testset "Simple Loops" begin
#     function hh0(x)
#         acc = 0
#         i = 1
#         while i <= 10
#             acc += x
#         end
#         acc
#     end

#     function hh1(x)
#         acc = 0
#         i = 1
#         while i <= x
#             acc += 1
#             i += 1
#         end
#         acc
#     end

#     function hh2(x)
#         acc = 0
#         i = 1
#         while i <= x
#             acc += i
#             i += 1
#         end
#         acc
#     end
# end

# @testset "Complex Loops" begin
#     function h0(x)
#         acc = 0
#         for i in 1:10
#             acc += x
#         end
#         return acc
#     end

#     function h1(x)
#         acc = 0
#         for i in 1:x
#             acc += 1
#         end
#         return acc
#     end

#     function h2(x)
#         acc = 0
#         for i in 1:x
#             acc += i
#         end
#         return acc
#     end
# end
