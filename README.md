# Kissat

This is a user interface, in Julia, to the [Kissat](https://github.com/arminbiere/kissat) SAT solver.

It exposes all the functions of the C interface, in the same syntax but without the `kissat_`, and provides higher-level interfaces:
- A `RawSolver` object with `init`, `push!`, `append!`, `solve` and `values` methods
- a one-stop-shop `kissat` accepting a list of clauses
- a solver accepting arbitrary types and converting them to integer variables through a `Dict`. Variables can have any type except `Pair{T,Bool}`, and are indicated either as `T` or as `T => false` to indicate a negated variable. Clauses are either `Vector` with entries in `T` or `Pair{T,Bool}`, or special shortcuts `Pair{T / NTuple{N,T} / Vector{T},T / false}` for Horn clauses.

```julia
julia> using Kissat
julia> # simple clauses
julia> cnf = [[1, -5, 4], [-1, 5, 3, 4], [-3, -4]];
julia> kissat(cnf) # the 0 indicates that variable 2 is unused
5-element Array{Int64,1}:
  1
  0
  3
 -4
  5
julia> # either coffee with cream, or tea with milk
julia> cnf = [[:coffee,:tea],[:coffee=>false,:tea=>false],[:coffee=>false,:cream],:tea=>:milk]
julia> kissat(Symbol,cnf)
Dict{Symbol, Bool} with 4 entries:
  :cream  => 1
  :milk   => 1
  :tea    => 1
  :coffee => 0
```


