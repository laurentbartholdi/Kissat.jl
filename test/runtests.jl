using Kissat
using Test

@testset "Kissat.jl" begin
    cnf = [[1, -5, 4], [-1, 5, 3, 4], [-3, -4]];

    @test kissat(cnf) == [1,0,3,-4,5]

    cnf = [[:coffee,:tea],[:coffee=>false,:tea=>false],[:coffee=>false,:cream],:tea=>:milk]

    @test kissat(Symbol,cnf) == Dict(:cream => 1, :milk => 1, :tea => 1, :coffee => 0)
end
