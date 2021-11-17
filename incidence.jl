using ForwardDiff
using ForwardDiff: Dual

struct Diff
    i::Int
end

struct LinearCoeffMap
    coeffs::Dict{Union{Diff, Int}, Union{Int, Real, Missing}}
end
Base.convert(::Type{LinearCoeffMap}, d::Dict) = LinearCoeffMap(Dict{Union{Diff, Int}, Union{Int, Real, Missing}}(d))
Base.merge(a::LinearCoeffMap, b::Missing) = missing
Base.merge(a::Missing, b::LinearCoeffMap) = missing
Base.merge(a::Missing, b::Missing) = missing
function Base.merge(a::LinearCoeffMap, b::LinearCoeffMap)
    LinearCoeffMap(mergewith(+, a.coeffs, b.coeffs))
end
function Base.:-(lcm::LinearCoeffMap)
    LinearCoeffMap(Dict(a=>-b for (a,b) in  lcm.coeffs))
end

struct Incidence <: Real
    coeffs::Union{Missing, LinearCoeffMap}
    vars::BitSet
    ds::BitSet
end
Incidence() = Incidence(missing, BitSet(), BitSet())

Base.:-(a::Incidence, b::Incidence) = Incidence(merge(a.coeffs, -b.coeffs),
                                          union(a.vars, b.vars),
                                          union(a.ds, b.ds))

Base.:*(a::Incidence, b::Incidence) = Incidence(missing,
                                          union(a.vars, b.vars),
                                          union(a.ds, b.ds))

Base.:/(a::Incidence, b::Incidence) = Incidence(missing,
                                          union(a.vars, b.vars),
                                          union(a.ds, b.ds))

Base.:+(a::Incidence, b::Incidence) = Incidence(merge(a.coeffs, b.coeffs),
                                          union(a.vars, b.vars),
                                          union(a.ds, b.ds))

Base.:^(a::Incidence, b::Incidence) = Incidence(missing,
                                          union(a.vars, b.vars),
                                          union(a.ds, b.ds))

# TODO, could merge coeffs with equal coeffs in both branches
Base.max(a::Incidence, b::Incidence) = Incidence(missing,
                                          union(a.vars, b.vars),
                                          union(a.ds, b.ds))

dropcoeffs(i::Incidence) = Incidence(missing, i.vars, i.ds)

Base.:<(a::Incidence, b::Incidence) = missing
Base.sqrt(i::Incidence) = dropcoeffs(i)
Base.tanh(i::Incidence) = dropcoeffs(i)
Base.max(a::Dual{Nothing, Incidence, 7}, b::Float64) = a
Base.abs(a::Dual{Nothing, Incidence, 7}) = a
Base.log(i::Incidence) = dropcoeffs(i)
Base.tan(i::Incidence) = dropcoeffs(i)
Base.exp(i::Incidence) = dropcoeffs(i)
Base.sin(i::Incidence) = dropcoeffs(i)
Base.cos(i::Incidence) = dropcoeffs(i)
Base.abs(i::Incidence) = dropcoeffs(i)
Base.:-(i::Incidence) = Incidence(-i.coeffs, i.vars, i.ds)

Base.promote_rule(::Type{Incidence}, ::Type{<:Real}) = Incidence
Incidence(r::Real) = Incidence()

ddt(x) = isa(x, Dual) ? (x.partials[1]; x.partials[1]) : 0.0
function F((b1, b2), x)
    if b1
        Any[x[1] - exp(ddt(x[2])), ddt(x[1]) + ddt(x[2])*sin(ddt(x[2]))] 
    else
        Any[x[1] - log(x[2]) + ddt(x[1]) + ddt(x[2])*cos(ddt(x[2]))] 
    end
end

u = [Incidence(Dict(i=>1), BitSet(i), BitSet()) for i = 1:2]
du = [Incidence(Dict(Diff(i)=>1), BitSet(), BitSet(i)) for i = 1:2]

x = [Dual(u[1], du[1]); Dual(u[2], du[2])]
map(ForwardDiff.value, F((true, false), x))