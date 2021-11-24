CC = Core.Compiler

import .CC:
    #= cicache.jl =#
    # haskey,
    # get,
    # getindex,
    # setindex!,
    # push!,
    #= types.jl =#
    InferenceParams,
    OptimizationParams,
    get_world_counter,
    get_inference_cache,
    code_cache,
    lock_mi_inference,
    unlock_mi_inference,
    add_remark!,
    may_optimize,
    may_compress,
    may_discard_trees,
    verbose_stmt_info,
    bail_out_toplevel_call,
    bail_out_call,
    #= inferenceresult.jl =#
    cache_lookup,
    #= inferencestate.jl =#
    InferenceState,
    #= tfuncs.jl =#
    builtin_tfunction,
    return_type_tfunc,
    #= abstractinterpretation.jl =#
    abstract_call_gf_by_type,
    add_call_backedges!,
    abstract_call_method_with_const_args,
    const_prop_entry_heuristic,
    abstract_call_method,
    abstract_invoke,
    abstract_call,
    abstract_eval_special_value,
    abstract_eval_value,
    abstract_eval_statement,
    #= typeinfer.jl =#
    typeinf,
    _typeinf,
    finish,
    transform_result_for_cache,
    finish!,
    typeinf_edge,
    #= optimize.jl =#
    inlining_policy

# Test.jl integration
import Test:
    record

import Core:
    Builtin,
    Intrinsics,
    IntrinsicFunction,
    MethodMatch,
    LineInfoNode,
    CodeInfo,
    CodeInstance,
    MethodInstance,
    NewvarNode,
    GlobalRef,
    GotoNode,
    GotoIfNot,
    Const,
    SSAValue,
    SlotNumber,
    Argument,
    Slot,
    ReturnNode,
    SimpleVector,
    svec

import .CC:
    AbstractInterpreter,
    NativeInterpreter,
    InferenceResult,
    InternalCodeCache,
    OptimizationState,
    WorldRange,
    WorldView,
    Bottom,
    LimitedAccuracy,
    NOT_FOUND,
    MethodCallResult,
    MethodMatches,
    UnionSplitMethodMatches,
    MethodMatchInfo,
    UnionSplitInfo,
    ConstCallInfo,
    InvokeCallInfo,
    MethodLookupResult,
    VarState,
    VarTable,
    CallMeta,
    CFG,
    BasicBlock,
    slot_id,
    widenconst,
    ⊑,
    is_throw_call,
    tmerge,
    switchtupleunion,
    argtypes_to_type,
    singleton_type,
    argtype_by_index,
    argtype_tail,
    _methods_by_ftype,
    specialize_method,
    add_backedge!,
    add_mt_backedge!,
    compute_basic_blocks,
    may_invoke_generator,
    inlining_enabled,
    instanceof_tfunc,
    ignorelimited,
    argextype,
    ArgInfo

import Base:
    # @constprop,
    parse_input_line,
    unwrap_unionall,
    rewrap_unionall,
    uniontypes,
    @invokelatest,
    destructure_callex

import Base.Meta:
    _parse_string,
    lower

using LoweredCodeUtils
import LoweredCodeUtils:
    istypedef,
    ismethod,
    callee_matches,
    rng,
    print_with_code,
    pushall!,
    # NamedVar,
    # add_requests!,
    add_ssa_preds!,
    # add_named_dependencies!,
    find_typedefs,
    add_control_flow!,
    add_typedefs!



macro isexpr(ex, args...)
    ex   = esc(ex)
    args = map(esc, args)
    return :($(GlobalRef(Core, :isa))($(ex), $(GlobalRef(Core, :Expr))) && $(_isexpr_check)($(ex), $(args...)))
end

_isexpr_check(ex::Expr, head::Symbol)         = ex.head === head
_isexpr_check(ex::Expr, heads)                = in(ex.head, heads)
_isexpr_check(ex::Expr, head::Symbol, n::Int) = ex.head === head && length(ex.args) == n
_isexpr_check(ex::Expr, heads, n::Int)        = in(ex.head, heads) && length(ex.args) == n

macro invoke(ex)
    f, args, kwargs = destructure_callex(ex)
    arg2typs = map(args) do x
        if @isexpr(x, :macrocall) && first(x.args) === Symbol("@nospecialize")
            x = last(x.args)
        end
        @isexpr(x, :(::)) ? (x.args...,) : (x, GlobalRef(Core, :Any))
    end
    args, argtypes = first.(arg2typs), last.(arg2typs)
    return esc(:($(GlobalRef(Core, :invoke))($(f), Tuple{$(argtypes...)}, $(args...); $(kwargs...))))
end

const MAX_TYPEUNION_COMPLEXITY = 3
const MAX_TYPEUNION_LENGTH = 3
const MAX_INLINE_CONST_SIZE = 256

const WrappedSource = Union{CodeInfo,OptimizationState,Nothing}

# custom lattice element / wrapper for taint analysis
# `val` taints every element in `tainted`
# that is, we were able to statically determine that elements in `tainted` were derived from at least `val`
struct Taint
    val
    tainted::Vector{Any}
end

widenconst((; val)::Taint) = isa(val, Type) ? Type{val} : typeof(val)

# partial ordering for Taint elements
a::Taint ⊑ b::Taint = (a.val === b.val)

@nospecialize(a) ⊑ b::Taint = begin
    isa(a, LimitedAccuracy) && (a = a.typ)

    if isa(a, AnyConditional)
        a = Bool
    end

    if isa(a, PartialStruct)
        return a.typ === widenconst(b)
    elseif isa(a, Const)
        return isa(a.val, Taint) # XXX copied from CC.⊑ but this smells
    elseif isa(a, PartialOpaque)
        return widenconst(a) ⊑ b
    elseif isa(a, Type)
        return a === widencost(b)
    else
        return a === b
    end
end

a::Taint ⊑ @nospecialize(b) = begin
    isa(b, LimitedAccuracy)  && return false
    isa(b, AnyConditional) && return false
    isa(b, PartialStruct) && return false
    if isa(b, Const)
        b = b.val
    end

    # XXX this is brokenly conservative, just want to get things working
    return false
end

# until we have this more ironed out just widen to Any
tmerge(a::Taint, @nospecialize(b)) = tmerge(@nospecialize(a), b::Taint) = Any

# and similarly for tmeet
tmeet(a::Taint, @nospecialize(b)) = tmeet(@nospecialize(a), b::Taint) = Bottom

# XXX currently not using this approach and instead opting to use custom lattice element
mutable struct TaintReport
    report # result of our taint analysis
end
mutable struct CachedTaintReport
    report
end

const Reports = Vector{TaintReport}
const CachedReports = Vector{CachedTaintReport}

mutable struct TaintResult
    reports::Reports
    wrapped_source::WrappedSource
end

struct CachedTaintResult
    reports::CachedReports
    wrapped_source::WrappedSource
end

const AnyTaintResult = Union{TaintResult, CachedTaintResult}

mutable struct TaintAnalyzerState
    native::NativeInterpreter
    param_key::UInt
    caller_cache::Reports
    cacher::Union{Nothing, Pair{Symbol, InferenceResult}}
end

struct TaintAnalyzer <: AbstractInterpreter
    cache::Vector{TaintResult}
    native::NativeInterpreter
    state::TaintAnalyzerState
end
get_native(interp::TaintAnalyzer) = interp.native
get_cache_key(interp::TaintAnalyzer) = hash(interp.cache)
TaintAnalyzerState(analyzer::TaintAnalyzer) = analyzer.state

struct TaintCallResult
    result::InferenceResult
    analyzer::TaintAnalyzer
    source::String
end

function TaintAnalyzer(world = get_world_counter();
                       inf_params = nothing,
                       opt_params = nothing)
    isnothing(inf_params) && (inf_params = InferenceParams()) #default inference and opt params
    isnothing(opt_params) && (opt_params = OptimizationParams())

    state = TaintAnalyzerState(world; inf_params, opt_params)
    native = state.native
    cache = Vector{TaintResult}();
    return TaintAnalyzer(cache, native, state)
end

for fld in fieldnames(TaintAnalyzerState)
    getter = Symbol("get_", fld)
    setter = Symbol("set_", fld, '!')
    @eval (@__MODULE__) @inline $getter(analyzer::TaintAnalyzer)    = getfield(TaintAnalyzerState(analyzer), $(QuoteNode(fld)))
    @eval (@__MODULE__) @inline $setter(analyzer::TaintAnalyzer, v) = setfield!(TaintAnalyzerState(analyzer), $(QuoteNode(fld)), v)
end

function get_param_key(inf_params::InferenceParams)
    h = @static UInt === UInt64 ? 0xa49bd446c0a5d90e : 0xe45361ac
    h = hash(inf_params, h)
    return h
end

function maybe_initialize_caches!(analyzer::TaintAnalyzer)
    cache_key = get_cache_key(analyzer)
    if !haskey(TAINT_CACHE, cache_key)
        TAINT_CACHE[cache_key] = IdDict{MethodInstance,CodeInstance}()
    end
end

function TaintAnalyzerState(world::UInt = get_world_counter();
                            inf_params = nothing,
                            opt_params = nothing)

    isnothing(inf_params) && (inf_params = InferenceParams()) #default inference and opt params
    isnothing(opt_params) && (opt_params = OptimizationParams())

    native = NativeInterpreter(world; inf_params, opt_params)
    param_key = get_param_key(inf_params)
    caller_cache = Reports()

    return TaintAnalyzerState(native, param_key, caller_cache, nothing)
end

function TaintAnalyzer(analyzer::TaintAnalyzer, state::TaintAnalyzerState)
    cache = analyzer.cache
    native = get_native(analyzer)
    newanalyzer = TaintAnalyzer(cache, native, state)
    maybe_initialize_caches!(newanalyzer)
    return newanalyzer
end

function TaintAnalyzer(analyzer::T) where {T<:TaintAnalyzer}
    newstate = TaintAnalyzerState(get_world_counter(analyzer);
                             inf_params      = InferenceParams(analyzer),
                             opt_params      = OptimizationParams(analyzer)
                             )
    newanalyzer = TaintAnalyzer(analyzer, newstate)
    maybe_initialize_caches!(newanalyzer)
    return newanalyzer
end

# local cache
CC.get_inference_cache(interp::TaintAnalyzer) = interp.cache

# These are unchanged by our analysis, so just fallback to the native implementation
CC.InferenceParams(interp::TaintAnalyzer) = InferenceParams(get_native(interp))
CC.OptimizationParams(interp::TaintAnalyzer) = OptimizationParams(get_native(interp))
CC.get_world_counter(interp::TaintAnalyzer) = get_world_counter(get_native(interp))

function InferenceState(result::InferenceResult, cache::Symbol, analyzer::TaintAnalyzer)
    set_result!(result) # modify `result` for succeeding JET analysis
    return @invoke InferenceState(result::InferenceResult, cache::Symbol, analyzer::AbstractInterpreter)
end

function set_result!(result::InferenceResult)
    init = TaintResult(TaintReport[], nothing)
    set_result!(result, init)
end
function set_result!(result::InferenceResult, taintresult::TaintResult)
    result.src = taintresult
end
function set_source!(result::InferenceResult, source::Union{CodeInfo,OptimizationState,Nothing})
    new = TaintResult(get_reports(result), source)
    set_result!(result, new)
end
function set_cached_result!(result::InferenceResult, cache::CachedReports)
    result.src = CachedTaintResult(cache, get_source(result.src::TaintResult))
end
get_reports((; src)::InferenceResult) = get_reports(src::TaintResult)
get_reports(result::TaintResult) = result.reports
get_cached_reports((; src)::InferenceResult) = get_cached_reports(src::CachedTaintResult)
get_cached_reports(result::CachedTaintResult) = result.reports
get_source((; src)::InferenceResult) = get_source(src::AnyTaintResult)
get_source(taintresult::AnyTaintResult) = taintresult.wrapped_source

"""
    add_new_report!(result::InferenceResult, report::InferenceErrorReport)
Adds new [`report::InferenceErrorReport`](@ref InferenceErrorReport) to `result::InferenceResult`.
`result.src` is supposed to be [`JETResult`](@ref).
"""
add_new_report!(result::InferenceResult, report::TaintReport) =
    return add_new_report!(get_reports(result), report)
add_new_report!(reports::Reports, report::TaintReport) =
    (push!(reports, report); return report)

add_cached_report!(caller, cached::CachedTaintReport) =
    return add_new_report!(caller, restore_cached_report(cached))

add_caller_cache!(analyzer::TaintAnalyzer, report::TaintReport) =
    return push!(get_caller_cache(analyzer), report)
add_caller_cache!(analyzer::TaintAnalyzer, reports::Reports) =
    return append!(get_caller_cache(analyzer), reports)

function analyze_frame!(analyzer::TaintAnalyzer, frame::InferenceState)
    typeinf(analyzer, frame)
    return analyzer, frame.result
end

# Overrides of abstract interpretation functions
CC.bail_out_toplevel_call(analyzer::TaintAnalyzer, @nospecialize(sig), sv) = false

function CC.abstract_eval_special_value(analyzer::TaintAnalyzer, @nospecialize(e), vtypes::VarTable, sv::InferenceState)
    ret = @invoke CC.abstract_eval_special_value(analyzer::AbstractInterpreter, e, vtypes::VarTable, sv::InferenceState)
    return ret
end

function CC.abstract_eval_value(analyzer::TaintAnalyzer, @nospecialize(e), vtypes::VarTable, sv::InferenceState)
    ret = @invoke CC.abstract_eval_value(analyzer::AbstractInterpreter, e, vtypes::VarTable, sv::InferenceState)
    return ret
end

function CC.abstract_eval_statement(analyzer::TaintAnalyzer, @nospecialize(e), vtypes::VarTable, sv::InferenceState)
    return @invoke CC.abstract_eval_statement(analyzer::AbstractInterpreter, e, vtypes::VarTable, sv::InferenceState)
end

function CC.builtin_tfunction(analyzer::TaintAnalyzer, @nospecialize(f), argtypes::Array{Any,1}, sv::InferenceState)
    ret = @invoke CC.builtin_tfunction(analyzer::AbstractInterpreter, f, argtypes::Array{Any,1},
                                       sv::Union{InferenceState,Nothing})
    return ret
end

function collect_callee_reports!(analyzer::TaintAnalyzer, sv::InferenceState)
    reports = get_caller_cache(analyzer)
    if !isempty(reports)
        #vf = get_virtual_frame(sv)
        for report in reports
            #pushfirst!(report.vst, vf)
            add_new_report!(sv.result, report)
        end
        empty!(reports)
    end
end

function CC.abstract_call_method(analyzer::TaintAnalyzer, method::Method, @nospecialize(sig), sparams::SimpleVector, hardlimit::Bool, sv::InferenceState)
    # here we should create and inject Taint elements
    # println("method sig : ", method.sig)
    # println("sig : ", sig)
    ret = @invoke CC.abstract_call_method(analyzer::AbstractInterpreter, method::Method, sig, sparams::SimpleVector, hardlimit::Bool, sv::InferenceState)
    #collect_callee_reports!(analyzer, sv)
    return ret
end

function CC.abstract_call_method_with_const_args(analyzer::TaintAnalyzer, result::MethodCallResult,
                                                 @nospecialize(f), arginfo::ArgInfo, match::MethodMatch,
                                                 sv::InferenceState, va_override::Bool)
    set_cacher!(analyzer, :abstract_call_method_with_const_args => sv.result)
    const_result =
        @invoke CC.abstract_call_method_with_const_args(analyzer::AbstractInterpreter, result::MethodCallResult,
                                                        @nospecialize(f), arginfo::ArgInfo, match::MethodMatch,
                                                        sv::InferenceState, va_override::Bool)
    set_cacher!(analyzer, nothing)
    if const_result !== nothing
        # successful constant prop', we also need to update reports
        collect_callee_reports!(analyzer, sv)
    end
    return const_result
end

function CC.abstract_call(analyzer::TaintAnalyzer, arginfo::ArgInfo,
                          sv::InferenceState, max_methods::Int = InferenceParams(analyzer).MAX_METHODS)
    # println("inside abstract_call, arginfo.fargs = ", arginfo.fargs)
    ret = @invoke CC.abstract_call(analyzer::AbstractInterpreter, arginfo::ArgInfo,
                                   sv::InferenceState, max_methods::Int)
    return ret
end


function CC.return_type_tfunc(analyzer::TaintAnalyzer, argtypes::Vector{Any}, sv::InferenceState)
    result = sv.result
    result0 = result.src::TaintResult
    set_result!(result)
    ret = @invoke return_type_tfunc(analyzer::AbstractInterpreter, argtypes::Vector{Any}, sv::InferenceState)
    set_result!(sv.result, result0)
    return ret
end

# cache
# =====

# global
# ------

"""
Keeps `src::CodeInstance` cache associated with `mi::MethodInstace` that represents the
analysis result on `mi` performed by [`analyzer::AbstractAnalyzer`](@ref AbstractAnalyzer),
where [`src.inferred::JETCachedResult`](@ref JETCachedResult) caches JET's analysis result.
This cache is separated by the identities of `AbstractAnalyzer`s, which are hash keys
computed by [`get_cache_key(analyzer::AbstractAnalyzer)`](@ref get_cache_key).
`JET_CACHE` is completely separated from the `NativeInterpreter`'s global cache, so that
JET's analysis never interacts with actual code execution.
"""
const TAINT_CACHE = IdDict{UInt, IdDict{MethodInstance,CodeInstance}}()

# just used for interactive developments
__clear_caches!() = empty!(TAINT_CACHE)

function CC.code_cache(analyzer::TaintAnalyzer)
    cache  = GlobalTaintCache(analyzer)
    worlds = WorldRange(get_world_counter(analyzer))
    return WorldView(cache, worlds)
end

struct GlobalTaintCache{Analyzer<:TaintAnalyzer}
    analyzer::Analyzer
end

function taint_cache(analyzer::TaintAnalyzer)
    TAINT_CACHE[get_cache_key(analyzer)]
end
taint_cache(wvc::WorldView{<:GlobalTaintCache}) = taint_cache(wvc.cache.analyzer)

CC.haskey(wvc::WorldView{<:GlobalTaintCache}, mi::MethodInstance) = haskey(taint_cache(wvc), mi)

function CC.typeinf_edge(analyzer::TaintAnalyzer, method::Method, @nospecialize(atypes), sparams::SimpleVector, caller::InferenceState)
    set_cacher!(analyzer, :typeinf_edge => caller.result)
    return @invoke typeinf_edge(analyzer::AbstractInterpreter, method::Method, @nospecialize(atypes), sparams::SimpleVector, caller::InferenceState)
end

function CC.get(wvc::WorldView{<:GlobalTaintCache}, mi::MethodInstance, default)
    codeinf = get(taint_cache(wvc), mi, default) # will ignore native code cache for a `MethodInstance` that is not analyzed by JET yet

    analyzer = wvc.cache.analyzer

    # # XXX this relies on a very dirty analyzer state manipulation, the reason for this is
    # # that this method (and `code_cache(::TaintAnalyzer)`) can be called from multiple
    # # contexts including edge inference, constant prop' heuristics and inlining, where we
    # # want to use report cache only in edge inference, but we can't tell which context is
    # # the caller of this specific method call here and thus can't tell whether we should
    # # enable report cache reconstruction without the information
    # # XXX move this logic into `typeinf_edge` ?
    cacher = get_cacher(analyzer)
    if isa(cacher, Pair{Symbol,InferenceResult})
        setter, caller = cacher
        if setter === :typeinf_edge
            if isa(codeinf, CodeInstance)
                # cache hit, now we need to append cached reports associated with this `MethodInstance`
                for cached in get_cached_reports(codeinf.inferred::CachedTaintResult)
                    restored = add_cached_report!(caller, cached)
                    add_caller_cache!(analyzer, restored) # should be updated in `abstract_call` (after exiting `typeinf_edge`)
                end
            end
            set_cacher!(analyzer, nothing)
        end
    end

    return codeinf
end

function CC.getindex(wvc::WorldView{<:GlobalTaintCache}, mi::MethodInstance)
    r = CC.get(wvc, mi, nothing)
    r === nothing && throw(KeyError(mi))
    return r::CodeInstance
end

function CC.transform_result_for_cache(analyzer::TaintAnalyzer, linfo::MethodInstance,
                                       valid_worlds::WorldRange, @nospecialize(inferred_result))
    taint_result = inferred_result::TaintResult
    cache = CachedTaintReport[]
    for report in get_reports(taint_result)
        cache_report!(cache, report)
    end
    # cache results from taint_result
    return CachedTaintResult(cache, get_source(taint_result))
end

function CC.setindex!(wvc::WorldView{<:GlobalTaintCache}, ci::CodeInstance, mi::MethodInstance)
    setindex!(taint_cache(wvc), ci, mi)
    return nothing
end

# local
# -----

struct LocalTaintCache{Analyzer<:TaintAnalyzer}
    analyzer::Analyzer
    cache::Vector{InferenceResult}
end

CC.get_inference_cache(analyzer::TaintAnalyzer) = LocalTaintCache(analyzer, get_inference_cache(get_native(analyzer)))

function CC.cache_lookup(linfo::MethodInstance, given_argtypes, cache::LocalTaintCache)
    # XXX the very dirty analyzer state observation again
    # this method should only be called from the single context i.e. `abstract_call_method_with_const_args`,
    # and so we should reset the cacher immediately we reach here
    analyzer = cache.analyzer
    setter, caller = get_cacher(analyzer)::Pair{Symbol,InferenceResult}
    @assert setter === :abstract_call_method_with_const_args
    set_cacher!(analyzer, nothing)

    inf_result = cache_lookup(linfo, given_argtypes, cache.cache)

    isa(inf_result, InferenceResult) || return inf_result

    # constant prop' hits a cycle (recur into same non-constant analysis), we just bail out
    isa(inf_result.result, InferenceState) && return inf_result

    # cache hit, try to restore local report caches

    # corresponds to the throw-away logic in `_typeinf(analyzer::TaintAnalyzer, frame::InferenceState)`
    #filter!(!is_from_same_frame(caller.linfo, linfo), get_reports(caller))

    for cached in get_cached_reports(inf_result)
        restored = add_cached_report!(caller, cached)
        add_caller_cache!(analyzer, restored) # should be updated in `abstract_call_method_with_const_args`
    end

    return inf_result
end

CC.push!(cache::LocalTaintCache, inf_result::InferenceResult) = CC.push!(cache.cache, inf_result)

# main driver
# ===========
function CC.typeinf(analyzer::TaintAnalyzer, frame::InferenceState)
    (; linfo, parent, result) = frame
    isentry = isnothing(parent)
    if isentry
        println("entry linfo : " , linfo.specTypes)
        #println("entry frame")
    end
    ret = @invoke typeinf(analyzer::AbstractInterpreter, frame::InferenceState)
    return ret
end

function CC._typeinf(analyzer::TaintAnalyzer, frame::InferenceState)
    CC.typeinf_nocycle(analyzer, frame) || return false # frame is now part of a higher cycle
    # with no active ip's, frame is done
    frames = frame.callers_in_cycle
    isempty(frames) && push!(frames, frame)
    valid_worlds = WorldRange()
    for caller in frames
        @assert !(caller.dont_work_on_me)
        caller.dont_work_on_me = true
        # might might not fully intersect these earlier, so do that now
        valid_worlds = CC.intersect(caller.valid_worlds, valid_worlds)
    end
    for caller in frames
        caller.valid_worlds = valid_worlds
        CC.finish(caller, analyzer)
        # finalize and record the linfo result
        caller.inferred = true
    end
    # collect results for the new expanded frame
    results = Tuple{InferenceState, Vector{Any}, Bool}[
            ( frames[i],
              frames[i].stmt_edges[1]::Vector{Any},
              frames[i].cached )
        for i in 1:length(frames) ]
    empty!(frames)
    for (frame, _, _) in results
        caller = frame.result
        opt = get_source(caller)
        if opt isa OptimizationState # implies `may_optimize(analyzer) === true`
            result_type = caller.result
            @assert !(result_type isa LimitedAccuracy)
            CC.optimize(analyzer, opt, OptimizationParams(analyzer), result_type)
            # # COMBAK we may want to enable inlining ?
            # if opt.const_api
            #     # XXX: The work in ir_to_codeinf! is essentially wasted. The only reason
            #     # we're doing it is so that code_llvm can return the code
            #     # for the `return ...::Const` (which never runs anyway). We should do this
            #     # as a post processing step instead.
            #     CC.ir_to_codeinf!(opt)
            #     if result_type isa Const
            #         caller.src = result_type
            #     else
            #         @assert CC.isconstType(result_type)
            #         caller.src = Const(result_type.parameters[1])
            #     end
            # end
            caller.valid_worlds = CC.getindex((opt.inlining.et::CC.EdgeTracker).valid_worlds)
        end
    end

    for (frame, edges, cached) in results
        caller = frame.result
        valid_worlds = caller.valid_worlds
        if CC.last(valid_worlds) >= get_world_counter()
            # if we aren't cached, we don't need this edge
            # but our caller might, so let's just make it anyways
            CC.store_backedges(caller, edges)
        end
        CC.finish!(analyzer, frame)

        # XXX this is a dirty fix for performance problem, we need more "proper" fix
        # https://github.com/aviatesk/JET.jl/issues/75
        # unique!(aggregation_policy(analyzer), get_reports(caller))

        # global cache management
        # part 1: transform collected reports to `JETCachedResult` and put it into `CodeInstance.inferred`
        if cached #&& !istoplevel(frame)
            CC.cache_result!(analyzer, caller)
        end
        # part 2: register invalidation callback for JET cache
        # add_jet_callback!(caller.linfo)

        reports = get_reports(caller)
        if frame.parent !== nothing
            # inter-procedural handling: get back to the caller what we got from these results
            add_caller_cache!(analyzer, reports)

            # local cache management
            # TODO there are duplicated work here and `transform_result_for_cache`
            cache = CachedReports()
            for report in reports
                cache_report!(cache, report)
            end
            set_cached_result!(caller, cache)
        end
    end

    return true
end

function CC.finish(me::InferenceState, analyzer::TaintAnalyzer)
    # @invoke CC.finish(me::InferenceState, analyzer::AbstractInterpreter)
    # prepare to run optimization passes on fulltree
    s_edges = me.stmt_edges[1]
    if s_edges === nothing
        s_edges = me.stmt_edges[1] = []
    end
    for edges in me.stmt_edges
        edges === nothing && continue
        edges === s_edges && continue
        append!(s_edges, edges)
        empty!(edges)
    end
    if me.src.edges !== nothing
        append!(s_edges, me.src.edges::Vector{Any})
        me.src.edges = nothing
    end
    # inspect whether our inference had a limited result accuracy,
    # else it may be suitable to cache
    me.bestguess = CC.cycle_fix_limited(me.bestguess, me)
    limited_ret = me.bestguess isa LimitedAccuracy
    limited_src = false
    if !limited_ret
        gt = me.src.ssavaluetypes::Vector{Any}
        for j = 1:length(gt)
            gt[j] = gtj = CC.cycle_fix_limited(gt[j], me)
            if gtj isa LimitedAccuracy && me.parent !== nothing
                limited_src = true
                break
            end
        end
    end
    if limited_ret
        # a parent may be cached still, but not this intermediate work:
        # we can throw everything else away now
        set_source!(me.result, nothing)
        me.cached = false
        me.src.inlineable = false
        unlock_mi_inference(analyzer, me.linfo)
    elseif limited_src
        # a type result will be cached still, but not this intermediate work:
        # we can throw everything else away now
        set_source!(me.result, nothing)
        me.src.inlineable = false
    else
        # annotate fulltree with type information,
        # either because we are the outermost code, or we might use this later
        doopt = (me.cached || me.parent !== nothing)
        CC.type_annotate!(me, doopt)
        if doopt && may_optimize(analyzer)
            set_source!(me.result, OptimizationState(me, OptimizationParams(analyzer), analyzer))
        else
            set_source!(me.result, me.src::CodeInfo) # stash a convenience copy of the code (e.g. for reflection)
        end
    end
    me.result.valid_worlds = me.valid_worlds
    me.result.result = me.bestguess

    # if istoplevel(me)
    #     # find assignments of abstract global variables, and assign types to them,
    #     # so that later analysis can refer to them

    #     stmts = me.src.code
    #     cfg = compute_basic_blocks(stmts)
    #     assigns = Dict{Int,Bool}() # slot id => is this deterministic
    #     for (pc, stmt) in enumerate(stmts)
    #         if @isexpr(stmt, :(=))
    #             lhs = first(stmt.args)
    #             if isa(lhs, Slot)
    #                 slot = slot_id(lhs)
    #                 if is_global_slot(analyzer, slot)
    #                     isnd = is_assignment_nondeterministic(cfg, pc)

    #                     # COMBAK this approach is really not true when there're multiple
    #                     # assignments in different basic blocks
    #                     if haskey(assigns, slot)
    #                         assigns[slot] |= isnd
    #                     else
    #                         assigns[slot] = isnd
    #                     end
    #                 end
    #             end
    #         end
    #     end

    #     if !isempty(assigns)
    #         slottypes = collect_slottypes(me)
    #         for (slot, isnd) in assigns
    #             slotname = get_global_slots(analyzer)[slot]
    #             typ = slottypes[slot]
    #             set_abstract_global!(analyzer, get_toplevelmod(analyzer), slotname, typ, isnd, me)
    #         end
    #     end
    # end
end

function CC.finish!(analyzer::TaintAnalyzer, frame::InferenceState)
    caller = frame.result

    # transform optimized `IRCode` to optimized `CodeInfo`
    src = get_source(caller)
    if src isa OptimizationState # implies `may_optimize(analyzer) === true`
        opt = src
        @assert opt.ir !== nothing # `_typeinf(::TaintAnalyzer, ::InferenceState)` disabled `const_api`

        src = CC.ir_to_codeinf!(opt)
        set_source!(caller, src)
    end

    return src
end

# Entry points to analysis
macro analyze_call(ex0...)
    return InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :analyze_call, ex0)
end

function analyze_call(@nospecialize(f), @nospecialize(types = Tuple{}))
    ft = Core.Typeof(f)
    if isa(types, Type)
        u = unwrap_unionall(types)
        tt = rewrap_unionall(Tuple{ft, u.parameters...}, types)
    else
        tt = Tuple{ft, types...}
    end
    return analyze_call(tt)
end

function analyze_call(@nospecialize(tt::Type{<:Tuple});
                     analyzer::Type{Analyzer} = TaintAnalyzer,
                     source::Union{Nothing,AbstractString} = nothing) where {Analyzer<:TaintAnalyzer}
    analyzer = Analyzer()
    maybe_initialize_caches!(analyzer)
    analyzer, result = analyze_gf_by_type!(analyzer, tt)

    if isnothing(source)
        source = string(nameof(var"@analyze_call"), " ", sprint(show_tuple_as_call, Symbol(""), tt))
    end

    return TaintCallResult(result, analyzer, source)
end
function analyze_gf_by_type!(analyzer::TaintAnalyzer, @nospecialize(tt::Type{<:Tuple}); kwargs...)
    mm = get_single_method_match(tt, InferenceParams(analyzer).MAX_METHODS, get_world_counter(analyzer))
    return analyze_method_signature!(analyzer, mm.method, mm.spec_types, mm.sparams; kwargs...)
end

@inline function show_tuple_as_call(io::IO, name::Symbol, @nospecialize(sig::Type))
    @static if hasmethod(Base.show_tuple_as_call, (IO, Symbol, Type), (:demangle, :kwargs, :argnames, :qualified))
        Base.show_tuple_as_call(io, name, sig; qualified = true)
    else
        Base.show_tuple_as_call(io, name, sig, false, nothing, nothing, true)
    end
end

function get_single_method_match(@nospecialize(tt), lim, world)
    mms = _methods_by_ftype(tt, lim, world)
    @assert !isa(mms, Bool) "unable to find matching method for $(tt)"

    filter!(mm::MethodMatch->mm.spec_types===tt, mms)
    @assert length(mms) == 1 "unable to find single target method for $(tt)"

    return first(mms)::MethodMatch
end

analyze_method!(analyzer::TaintAnalyzer, m::Method; kwargs...) =
    analyze_method_signature!(analyzer, m, m.sig, method_sparams(m); kwargs...)

function method_sparams(m::Method)
    s = TypeVar[]
    sig = m.sig
    while isa(sig, UnionAll)
        push!(s, sig.var)
        sig = sig.body
    end
    return svec(s...)
end

function analyze_method_signature!(analyzer::TaintAnalyzer, m::Method, @nospecialize(atype), sparams::SimpleVector; kwargs...)
    mi = specialize_method(m, atype, sparams)::MethodInstance
    return analyze_method_instance!(analyzer, mi; kwargs...)
end

function analyze_method_instance!(analyzer::TaintAnalyzer, mi::MethodInstance;
                                  set_entry::Bool = true,
                                  )
    result = InferenceResult(mi)

    frame = InferenceState(result, #=cache=# :global, analyzer)

    isnothing(frame) && return analyzer, result

    #set_entry && set_entry!(analyzer, mi)
    return analyze_frame!(analyzer, frame)
end
