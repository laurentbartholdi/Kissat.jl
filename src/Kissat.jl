module Kissat

import Kissat_jll

export init, add, solve, value, kissat

import Base: show, convert, iterate, IteratorSize, push!, append!, values

const libkissat = Kissat_jll.libkissat

################################################################
# low-level interface

# the main structure
abstract type Solver end

mutable struct RawSolver <: Solver
    ptr::Ptr{Cvoid}
end
convert(::Type{Ptr{Cvoid}}, p::RawSolver) = p.ptr

# standard IPASIR interface

signature() = ccall((:kissat_signature, libkissat), Cstring, ()) |> unsafe_string

"""init()::RawSolver

Low-level interface: creates a new solver object.
"""
__init() = RawSolver(ccall((:kissat_init, libkissat), Ptr{Cvoid}, ()))

"""add(kissat::RawSolver, lit::Int)

Low-level interface: add a single literal to kissat, as part of a clause.
As usual, negative integers represent negated literals, and 0 terminates a clause.
"""
add(kissat::RawSolver, lit::Int) = ccall((:kissat_add, libkissat), Cvoid, (RawSolver, Cint), kissat, lit)

"""solve(kissat::RawSolver)::Symbol

Low-level interface: solve the current problem. Returns :undefined, :satisfiable or :unsatisfiable according to the problem status.
"""
solve(kissat::RawSolver) = (v = ccall((:kissat_solve, libkissat), Cint, (RawSolver,), kissat); v == 0 ? :unknown : v == 10 ? :satisfiable : v == 20 ? :unsatisfiable : error("Unknown return value $v from kissat_solve"))

"""value(kissat::RawSolver, lit::Int)::Int

Low-level interface: queries the value of lit in the current solution.
"""
value(kissat::RawSolver, lit::Int) = ccall((:kissat_value, libkissat), Cint, (RawSolver,Cint), kissat, lit) |> Int

"""release(kissat::RawSolver)::Int

Low-level interface: frees the object kissat.
"""
release(kissat::RawSolver) = ccall((:kissat_release, libkissat), Cvoid, (RawSolver,), kissat)

"""set_terminate(kissat::RawSolver, state::???, terminate::Function)::Int

Low-level interface: frees the object kissat.
"""
set_terminate(kissat::RawSolver, state::Ptr{Cvoid}, terminate::Function) = ccall((:kissat_set_terminate, libkissat), Cvoid, (RawSolver,Ptr{Cvoid},Ptr{Cvoid}), kissat, state, cfunction(terminate,Cint,(Ptr{Cvoid},)))

# Additional API functions.

terminate(kissat::RawSolver) = ccall((:kissat_terminate, libkissat), Cvoid, (RawSolver,), kissat)

reserve(kissat::RawSolver, max_var::Int) = (kissat.max_var = max_var; ccall((:kissat_reserve, libkissat), Cvoid, (RawSolver,Cint), kissat, max_var))

id() = ccall((:kissat_id, libkissat), Cstring, ()) |> unsafe_string

version() = ccall((:kissat_version, libkissat), Cstring, ()) |> unsafe_string

compiler() = ccall((:kissat_compiler, libkissat), Cstring, ()) |> unsafe_string

get_option(kissat::RawSolver, name::String) = ccall((:kissat_get_option, libkissat), Cint, (RawSolver, Cstring), kissat, name) |> Int

set_option(kissat::RawSolver, name::String, new_value::Int) = ccall((:kissat_set_option, libkissat), Cint, (RawSolver, Cstring, Cint), kissat, name, new_value) |> Int

has_configuration(name::String) = ccall((:kissat_has_configuration, libkissat), Cint, (Cstring,), name) |> Bool

set_configuration(kissat::RawSolver, name::String) = ccall((:kissat_set_configuration, libkissat), Cint, (RawSolver, Cstring), kissat, name) |> Bool

copyright() = (a = unsafe_wrap(Array{Cstring},ccall((:kissat_copyright, Kissat.libkissat), Ptr{Cstring}, ()),(1,)); "find length of array"; a .|> unsafe_string)

build(line_prefix::String) = ccall((:kissat_build, libkissat), Cvoid, (Cstring,), line_prefix)

banner(line_prefix::String, name_of_app::String) = ccall((:kissat_build, libkissat), Cvoid, (Cstring,Cstring), line_prefix, name_of_app)

set_conflict_limit(kissat::RawSolver, limit::Int) = ccall((:kissat_set_conflict_limit, libkissat), Cint, (RawSolver, Cuint), kissat, limit) |> Int

set_decision_limit(kissat::RawSolver, limit::Int) = ccall((:kissat_set_decision_limit, libkissat), Cint, (RawSolver, Cuint), kissat, limit) |> Int

print_statistics(kissat::RawSolver) = ccall((:kissat_print_statistics, libkissat), Cvoid, (RawSolver,), kissat)

################################################################
#

""" options:
  --ands=<bool>              extract and eliminate and gates [true]
  --backbone=0..2            binary clause backbone (2=eager) [1]
  --backboneeffort=0..1e5    effort in per mille [20]
  --backbonemaxrounds=1...   maximum backbone rounds [1e3]
  --backbonerounds=1...      backbone rounds limit [100]
  --bump=<bool>              enable variable bumping [true]
  --bumpreasons=<bool>       bump reason side literals too [true]
  --bumpreasonslimit=1...    relative reason literals limit [10]
  --bumpreasonsrate=1...     decision rate limit [10]
  --chrono=<bool>            allow chronological backtracking [true]
  --chronolevels=0...        maximum jumped over levels [100]
  --compact=<bool>           enable compacting garbage collection [true]
  --compactlim=0..100        compact inactive limit (in percent) [10]
  --decay=1..200             per mille scores decay [50]
  --definitioncores=1..100   how many cores [2]
  --definitions=<bool>       extract general definitions [true]
  --definitionticks=0...     kitten ticks limits [1e6]
  --defraglim=50..100        usable defragmentation limit in percent [75]
  --defragsize=10...         size defragmentation limit [2^18]
  --eliminate=<bool>         bounded variable elimination (BVE) [true]
  --eliminatebound=0..2^13   maximum elimination bound [16]
  --eliminateclslim=1...     elimination clause size limit [100]
  --eliminateeffort=0..2e3   effort in per mille [100]
  --eliminateinit=0...       initial elimination interval [500]
  --eliminateint=10...       base elimination interval [500]
  --eliminateocclim=0...     elimination occurrence limit [2e3]
  --eliminaterounds=1..1e4   elimination rounds limit [2]
  --emafast=10..1e6          fast exponential moving average window [33]
  --emaslow=100..1e6         slow exponential moving average window [1e5]
  --equivalences=<bool>      extract and eliminate equivalence gates [true]
  --extract=<bool>           extract gates in variable elimination [true]
  --forcephase=<bool>        force initial phase [false]
  --forward=<bool>           forward subsumption in BVE [true]
  --forwardeffort=0..1e6     effort in per mille [100]
  --ifthenelse=<bool>        extract and eliminate if-then-else gates [true]
  --incremental=<bool>       enable incremental solving [false]
  --mineffort=0...           minimum absolute effort in millions [10]
  --minimize=<bool>          learned clause minimization [true]
  --minimizedepth=1..1e6     minimization depth [1e3]
  --minimizeticks=<bool>     count ticks in minimize and shrink [true]
  --modeinit=10..1e8         initial focused conflicts limit [1e3]
  --otfs=<bool>              on-the-fly strengthening [true]
  --phase=<bool>             initial decision phase [true]
  --phasesaving=<bool>       enable phase saving [true]
  --probe=<bool>             enable probing [true]
  --probeinit=0...           initial probing interval [100]
  --probeint=2...            probing interval [100]
  --profile=0..4             profile level [2]
  --promote=<bool>           promote clauses [true]
  --quiet=<bool>             disable all messages [false]
  --reduce=<bool>            learned clause reduction [true]
  --reducefraction=10..100   reduce fraction in percent [75]
  --reduceinit=2..1e5        initial reduce interval [1e3]
  --reduceint=2..1e5         base reduce interval [1e3]
  --reluctant=<bool>         stable reluctant doubling restarting [true]
  --reluctantint=2..2^15     reluctant interval [2^10]
  --reluctantlim=0..2^30     reluctant limit (0=unlimited) [2^20]
  --rephase=<bool>           reinitialization of decision phases [true]
  --rephaseinit=10..1e5      initial rephase interval [1e3]
  --rephaseint=10..1e5       base rephase interval [1e3]
  --restart=<bool>           enable restarts [true]
  --restartint=1..1e4        base restart interval [1]
  --restartmargin=0..25      fast/slow margin in percent [10]
  --seed=0...                random seed [0]
  --shrink=0..3              learned clauses (1=bin,2=lrg,3=rec) [3]
  --simplify=<bool>          enable probing and elimination [true]
  --stable=0..2              enable stable search mode [1]
  --statistics=<bool>        print complete statistics [false]
  --substitute=<bool>        equivalent literal substitution [true]
  --substituteeffort=1..1e3  effort in per mille [10]
  --substituterounds=1..100  maximum substitution rounds [2]
  --subsumeclslim=1...       subsumption clause size limit [1e3]
  --subsumeocclim=0...       subsumption occurrence limit [1e3]
  --sweep=<bool>             enable SAT sweeping [true]
  --sweepclauses=0...        environment clauses [2^10]
  --sweepdepth=0...          environment depth [1]
  --sweepeffort=0..1e4       effort in per mille [10]
  --sweepfliprounds=0...     flipping rounds [1]
  --sweepmaxclauses=2...     maximum environment clauses [2^12]
  --sweepmaxdepth=1...       maximum environment depth [2]
  --sweepmaxvars=2...        maximum environment variables [2^7]
  --sweepvars=0...           environment variables [2^7]
  --target=0..2              target phases (1=stable,2=focused) [1]
  --tier1=1..100             learned clause tier one glue limit [2]
  --tier2=1..1e3             learned clause tier two glue limit [6]
  --tumble=<bool>            tumbled external indices order [true]
  --verbose=0..3             verbosity level [0]
  --vivify=<bool>            vivify clauses [true]
  --vivifyeffort=0..1e3      effort in per mille [100]
  --vivifyirred=1..100       relative irredundant effort [1]
  --vivifytier1=1..100       relative tier1 effort [3]
  --vivifytier2=1..100       relative tier2 effort [6]
  --walkeffort=0..1e6        effort in per mille [50]
  --walkinitially=<bool>     initial local search [false]
  --warmup=<bool>            initialize phases by unit propagation [true]
      """

nothing

""" configurations:
  --basic    basic CDCL solving ('--plain' but no restarts, minimize, reduce)
  --default  default configuration
  --plain    plain CDCL solving without advanced techniques
  --sat      target satisfiable instances ('--target=2 --restartint=50')
  --unsat    target unsatisfiable instances ('--stable=0')
"""

const configurations = Set([:basic,:default,:plain,:sat,:unsat])

################################################################
# higher-level interface, with automatic destruction and one-go clause addition

"""new(clauses; max_var::Int = 0, configuration = nothing)::RawSolver

Creates a new solver, that self-destructs at end of life.

The optional arguments may specify a prereserved number max_var of literals,
and a configuration in $configurations."""
function init(max_var::Int = 0, configuration = nothing)
    p = __init()
    if isa(configuration,Symbol) && configuration∈configurations
        configuration = String(configuration)
    end
    if isa(configuration,String)
        set_configuration(p, configuration) || error("Could not set configuration $configuration")
    elseif configuration≠nothing
        error("Invalid configuration $configuration")
    end
    max_var > 0 && reserve(p, max_var)
    finalizer(release, p)
    p
end

function Base.show(io::IO, kissat::RawSolver)
    if kissat.ptr == C_NULL
        print(io, "Unallocated Kissat solver")
    else
        print(io, "Kissat solver")
    end
end

function Base.push!(kissat::RawSolver, clause)
    for c=clause
        add(kissat, c)
    end
    add(kissat, 0)
end

function Base.append!(kissat::Solver, clauses)
    for clause=clauses
        push!(kissat, clause)
    end
end

function Base.values(kissat::RawSolver, range)
    [value(kissat,i) for i=range]
end

function Base.values(kissat::RawSolver)
    v = Int[]
    i = 1
    while true
        c = value(kissat,i)
        c==0 && return v
        push!(v,c)
        i += 1
    end
end

"""Your one-stop shop."""
function kissat(clauses; args...)
    p = init(; args...)
    append!(p, clauses)
    r = solve(p)
    r == :unsatisfiable ? r : values(p,1:maximum(maximum(abs.(c)) for c=clauses))
end

################################################################
struct TypedSolver{T} <: Solver
    kissat::RawSolver
    dict::Dict{T,Int}
    tcid::Vector{T}
end

"""init(T::Type; ...)

Same as init, except that the literals should now be of type T.

push! and append! add one, respectively many clauses, each of which
is an enumerable object consisting of objects of type T or Pair{T,Bool}
to express negated variables."""
function init(T::Type; args...)
    p = TypedSolver{T}(init(; args...), Dict(), [])
    p
end

function Base.show(io::IO, p::TypedSolver{T}) where T
    print(io, p.kissat, "{$T}($(length(p.tcid)) literals)")
end

function Base.push!(p::TypedSolver{T}, clause) where T
    for c=clause
        v = true
        if isa(c,Pair{T,Bool})
            c.second && error("Clause format should be :T or :T=>false")
            (c,v) = c
        end
        if haskey(p.dict,c)
            ic = p.dict[c]
        else
            push!(p.tcid,c)
            p.dict[c] = ic = length(p.tcid)
        end
        add(p.kissat, v ? ic : -ic)
    end
    add(p.kissat, 0)
end

Base.push!(p::TypedSolver{T}, c::T) where T = push!(p, [c])
Base.push!(p::TypedSolver{T}, c::Pair{T,Bool}) where T = push!(p, [c])
Base.push!(p::TypedSolver{T}, c::Pair{T,T}) where T = push!(p, [c.first=>false,c.second])
Base.push!(p::TypedSolver{T}, c::Union{Pair{NTuple{N,T},Bool},Pair{Vector{T},Bool}}) where {T,N} = push!(p, [x=>c.second for x=c.first])
Base.push!(p::TypedSolver{T}, c::Union{Pair{NTuple{N,T},T},Pair{Vector{T},T}}) where {T,N} = push!(p, [[x=>false for x=c.first]; c.second])

solve(p::TypedSolver) = solve(p.kissat)

function value(p::TypedSolver{T}, c::T) where T
    value(p.kissat, p.dict[c])
end

int2bool(v) = (v > 0 ? true : (v < 0 ? false : nothing))
               
"""values(p::TypedSolver, range=keys(p.dict)

Returns the values found by the solver, as a Dict{T,Int}.
A value is >0 if and only if the variable is true in the solution."""
function Base.values(p::TypedSolver, range=keys(p.dict))
    Dict(c => int2bool(value(p,c)) for c=range)
end

"""kissat(T::Type, clauses; ...)

Your one-stop shop to solve SAT systems.
Performs init, append, solve, values in order, and returns
:unsatisfiable or a solution."""
function kissat(T::Type, clauses; args...)
    p = init(T; args...)
    append!(p, clauses)
    r = solve(p)
    r == :unsatisfiable ? r : values(p)
end

################################################################
# iterator

# this is useless, because kissat does not support iterative solving
function Base.iterate(kissat::RawSolver, state=nothing)
    if solve(kissat)==:satisfiable
        v = get_model(it.p)
        sol = [v[i] ? i : -i for i=1:length(v)]

        # add inverse sol for next iter
        add_clause(it.p, -sol)
        return (sol, nothing)
    else
        return nothing
    end
end

IteratorSize(it::RawSolver) = Base.SizeUnknown()

end
