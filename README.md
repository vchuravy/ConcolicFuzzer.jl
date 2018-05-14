# ConcolicFuzzer

Prototype of a fuzzer using concolic execution.
This project is based on Cassette and Julia 0.7-dev and since the former is experimental and the latter in development
no gurantees what so ever are given. 

## Requirements

- Julia 0.7-dev at 69e559d496c69c7909ba87631cb552295e77255
- Cassette.jl from https://github.com/vchuravy/Cassette.jl/tree/vc/iftransform

# Features
* Able to generate a trace of an arbitrary Julia progra.
  A trace is an execution of a whole program, with linearised control-flow
* We are able to "taint" input variables to generate traces that are concolic in nature
* Can manually assert conditions
* automatically insert assert statements before branches
* verification of traces, so that concolic values are propagated
* reasoning about intrinsics/built-in functions is limited
* Experimental support for loops
* No support for functions that return tuples
* Very limited translation of traces to Z3 (only for programs using `<:Integer` )
* Support for tainting values generated by rand
* Allow for seeding of rand values to have deterministic execution
* Use values generated by rand function within program as a source of exploration.
* Use Z3 to generate input values that explore branches
* Iterate through all controlable or random controlled branches

# Limitations

*  Currently functions need to be manually annotated as leaf-functions for the taint analysis (see `src/tain.jl`).
   I would like to support generic taint of functions with the only leaf functions being Julia runtime intrinsics and built-ins.
   This requires recursive trace generation.
* Currently doesn't handle floats.
* No memory-model/No support for Arrays.
* `Bool` in Julia is a subtype of `Integer`, therefore arithmetic and comparision operations are
  defined. It is not clear to me how to translate that into SMT2. One possibility is translate
  all `Bool` to `(_ BitVec 1)`, but than we can no longer use them as output for comparision
  operations. This will require reasoning over Julia's type system in the solver...