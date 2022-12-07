using Kissat
using Test

@testset "Kissat.jl" begin
    p = init()
    append!(p,[[1, -5, 4], [-1, 5, 3, 4], [-3, -4]])
    @test solve(p) == :satisfiable
    p = init(Int)
    push!(p,[1,2])
    @test Set(collect(p)) == Set([[1,2],[-1,2],[1,-2]])
end
