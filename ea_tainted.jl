module TaintAnalysis

# let
#     README = normpath(dirname(@__DIR__), "README.md")
#     include_dependency(README)
#     @doc read(README, String) EscapeAnalysis
# end

export
    analyze_escapes,
    @analyze_escapes

import Core:
    CodeInfo,
    CodeInstance,
    MethodInstance,
    Const,
    Argument,
    SSAValue,
    PiNode,
    PhiNode,
    UpsilonNode,
    PhiCNode,
    ReturnNode,
    GotoNode,
    GotoIfNot,
    SimpleVector

const CC = Core.Compiler

import .CC:
    AbstractInterpreter,
    NativeInterpreter,
    WorldView,
    WorldRange,
    InferenceParams,
    OptimizationParams,
    get_world_counter,
    get_inference_cache,
    lock_mi_inference,
    unlock_mi_inference,
    add_remark!,
    may_optimize,
    may_compress,
    may_discard_trees,
    verbose_stmt_info,
    code_cache,
    get_inference_cache,
    OptimizationState,
    IRCode,
    optimize,
    widenconst,
    argextype,
    singleton_type,
    IR_FLAG_EFFECT_FREE,
    is_meta_expr_head

import Base: ==

import Base.Meta: isexpr

using InteractiveUtils
#using IRTools

# let __init_hooks__ = []
#     global __init__() = foreach(f->f(), __init_hooks__)
#     global register_init_hook!(@nospecialize(f)) = push!(__init_hooks__, f)
# end

mutable struct TaintAnalyzer{State} <: AbstractInterpreter
    native::NativeInterpreter
    ir::IRCode
    state::State
    linfo::MethodInstance
    TaintAnalyzer(native::NativeInterpreter) = new{TaintState}(native)
end

CC.InferenceParams(interp::TaintAnalyzer)    = InferenceParams(interp.native)
CC.OptimizationParams(interp::TaintAnalyzer) = OptimizationParams(interp.native)
CC.get_world_counter(interp::TaintAnalyzer)  = get_world_counter(interp.native)

CC.lock_mi_inference(::TaintAnalyzer,   ::MethodInstance) = nothing
CC.unlock_mi_inference(::TaintAnalyzer, ::MethodInstance) = nothing

CC.add_remark!(interp::TaintAnalyzer, sv, s) = add_remark!(interp.native, sv, s)

CC.may_optimize(interp::TaintAnalyzer)      = may_optimize(interp.native)
CC.may_compress(interp::TaintAnalyzer)      = may_compress(interp.native)
CC.may_discard_trees(interp::TaintAnalyzer) = may_discard_trees(interp.native)
CC.verbose_stmt_info(interp::TaintAnalyzer) = verbose_stmt_info(interp.native)

CC.get_inference_cache(interp::TaintAnalyzer) = get_inference_cache(interp.native)

const GLOBAL_CODE_CACHE = IdDict{MethodInstance,CodeInstance}()
__clear_code_cache!() = empty!(GLOBAL_CODE_CACHE)

function CC.code_cache(interp::TaintAnalyzer)
    worlds = WorldRange(get_world_counter(interp))
    return WorldView(GlobalCache(), worlds)
end

struct GlobalCache end

CC.haskey(wvc::WorldView{GlobalCache}, mi::MethodInstance) = haskey(GLOBAL_CODE_CACHE, mi)

CC.get(wvc::WorldView{GlobalCache}, mi::MethodInstance, default) = get(GLOBAL_CODE_CACHE, mi, default)

CC.getindex(wvc::WorldView{GlobalCache}, mi::MethodInstance) = getindex(GLOBAL_CODE_CACHE, mi)

function CC.setindex!(wvc::WorldView{GlobalCache}, ci::CodeInstance, mi::MethodInstance)
    GLOBAL_CODE_CACHE[mi] = ci
    add_callback!(mi) # register the callback on invalidation
    return nothing
end

function add_callback!(linfo)
    if !isdefined(linfo, :callbacks)
        linfo.callbacks = Any[invalidate_cache!]
    else
        if !any(@nospecialize(cb)->cb===invalidate_cache!, linfo.callbacks)
            push!(linfo.callbacks, invalidate_cache!)
        end
    end
    return nothing
end

function invalidate_cache!(replaced, max_world, depth = 0)
    delete!(GLOBAL_CODE_CACHE, replaced)

    if isdefined(replaced, :backedges)
        for mi in replaced.backedges
            mi = mi::MethodInstance
            if !haskey(GLOBAL_CODE_CACHE, mi)
                continue # otherwise fall into infinite loop
            end
            invalidate_cache!(mi, max_world, depth+1)
        end
    end
    return nothing
end

# analysis
# ========

"""
    x::EscapeLattice

A lattice for escape information, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates `x` has not been analyzed at all
- `x.ReturnEscape::Bool`: indicates `x` may escape to the caller via return (possibly as a field),
    where `x.ReturnEscape && 0 ∈ x.EscapeSites` has the special meaning that it's visible to
    the caller simply because it's passed as call argument
- `x.ThrownEscape::Bool`: indicates `x` may escape to somewhere through an exception (possibly as a field)
- `x.EscapeSites::BitSet`: records program counters (SSA numbers) where `x` can escape
- `x.ArgEscape::Int` (not implemented yet): indicates it will escape to the caller through `setfield!` on argument(s)
  * `-1` : no escape
  * `0` : unknown or multiple
  * `n` : through argument N

These attributes can be combined to create a partial lattice that has a finite height, given
that input program has a finite number of statements, which is assured by Julia's semantics.

There are utility constructors to create common `EscapeLattice`s, e.g.,
- `NoEscape()`: the bottom element of this lattice, meaning it won't escape to anywhere
- `AllEscape()`: the topmost element of this lattice, meaning it will escape to everywhere

The escape analysis will transition these elements from the bottom to the top,
in the same direction as Julia's native type inference routine.
An abstract state will be initialized with the bottom(-like) elements:
- the call arguments are initialized as `ArgumentReturnEscape()`, because they're visible from a caller immediately
- the other states are initialized as `NotAnalyzed()`, which is a special lattice element that
  is slightly lower than `NoEscape`, but at the same time doesn't represent any meaning
  other than it's not analyzed yet (thus it's not formally part of the lattice).
"""
mutable struct TaintLattice
    Analyzed::Bool
    TaintedPC::BitSet # this element is directly tainted by statements at these locations in the methods stmts
    TaintedArg::BitSet # this element is directly tainted by arguments at these locations in the methods args
end

TaintLattice(latt::TaintLattice, new_pcs, new_args) = 
    TaintLattice(latt.Analyzed,
                union(latt.TaintedPC, new_pcs),
                union(latt.TaintedArg, new_args))

# precomputed default values in order to eliminate computations at each callsite
#const CLEAN = BitSet()
#const ARGUMENT_ESCAPE_SITES = BitSet(0)

# the constructors
# NotAnalyzed() = TaintLattice(false, BitSet(), BitSet()) # not formally part of the lattice
# Clean() = TaintLattice(true, BitSet(), BitSet()) # initialize arguments to initial call to this
# TaintedByPC(pc::Int) = TaintLattice(true, BitSet(pc), CLEAN)
# TaintedByArg(n::Int) = TaintLattice(true, CLEAN, BitSet(n))

# Convenience names for some ⊑ queries
# export
#     is_untainted,
#     is_tainted
is_untainted(x::TaintLattice) = x == Clean()
is_tainted(x::TaintLattice) = x.TaintedPC !== BitSet() || x.TaintedArg !== BitSet()
# end

function maybeAddTaint!(ele::TaintLattice, val)
    if isa(val, SSAValue)
        val = val.id
        push!(ele.TaintedPC, val)
    else 
        isa(val, Argument) || return 
        val = val.n
        push!(ele.TaintedArg, val)
    end
end


function addTaint!(ele::TaintLattice, pc, arg)
    if pc !== nothing
        isa(pc, SSAValue) && (pc = pc.id)
        push!(ele.TaintedPC, pc)
    end
    if arg !== nothing
        #println("arg ", arg, " tainted a stmt")
        push!(ele.TaintedArg, arg)
    end
    return ele
end

# we need to make sure this `==` operator corresponds to lattice equality rather than object equality,
# otherwise `propagate_changes` can't detect the convergence
x::TaintLattice == y::TaintLattice = begin
    return x.Analyzed === y.Analyzed &&
           x.TaintedPC === y.TaintedPC &&
           x.TaintedArg === y.TaintedArg
end

# x::EscapeLattice ⊑ y::EscapeLattice = begin
#     if x.Analyzed ≤ y.Analyzed &&
#        x.ReturnEscape ≤ y.ReturnEscape &&
#        x.ThrownEscape ≤ y.ThrownEscape &&
#        x.EscapeSites ⊆ y.EscapeSites &&
#        true
#         return true
#     end
#     return false
# end
# x::EscapeLattice ⊏ y::EscapeLattice = x ⊑ y && !(y ⊑ x)
# x::EscapeLattice ⋤ y::EscapeLattice = !(y ⊑ x)

# x::EscapeLattice ⊔ y::EscapeLattice = begin
#     return EscapeLattice(
#         x.Analyzed | y.Analyzed,
#         x.ReturnEscape | y.ReturnEscape,
#         x.ThrownEscape | y.ThrownEscape,
#         x.EscapeSites ∪ y.EscapeSites,
#         )
# end

# x::EscapeLattice ⊓ y::EscapeLattice = begin
#     return EscapeLattice(
#         x.Analyzed & y.Analyzed,
#         x.ReturnEscape & y.ReturnEscape,
#         x.ThrownEscape & y.ThrownEscape,
#         x.EscapeSites ∩ y.EscapeSites,
#         )
# end

"""
    state::EscapeState

Extended lattice that maps arguments and SSA values to escape information represented as `EscapeLattice`:
- `state.arguments::Vector{EscapeLattice}`: escape information about "arguments" – note that
  "argument" can include both call arguments and slots appearing in analysis frame
- `ssavalues::Vector{EscapeLattice}`: escape information about each SSA value
"""
struct TaintState
    #arguments::Vector{TaintLattice} # arguments[i] returns the ssavalues and arguments that taint the ith argument in the current IR
    ssavalues::Vector{TaintLattice} # ssavalues[i] gives you the ssavalues and arguments that taint the ith stmt in the current IR
end

# not currently used
function TaintState()
    TaintState(Vector{TaintLattice}(), Vector{TaintLattice}())
end

function TaintState(nstmts::Int, nargs::Int)
    #arguments = TaintLattice[TaintLattice(false, BitSet(), BitSet()) for _ in 1:nargs]
    ssavalues = TaintLattice[TaintLattice(false, BitSet(), BitSet()) for _ in 1:nstmts]
    return TaintState(ssavalues)
end

# instead of a single state, create multiple states, each corresponding to a control flow branch
function TaintState(state::TaintState, stmt, pc::Int)
    new_state = TaintState(state.ssavalues)
    lattices = new_state.ssavalues
    stmt_lattice = lattices[pc]
    if !stmt_lattice.Analyzed
        stmt_lattice.Analyzed = true
    end
    if isdefined(stmt, :args)
        for arg in stmt.args
            maybeAddTaint!(stmt_lattice, arg)
            # if isa(arg, Argument) # if an Argument is in the arguments of this stmt, consider this stmt tainted by that Argument
            #     #println("adding ", arg.n, " to TaintedArg of ", stmt_lattice)
            #     addTaint!(stmt_lattice, nothing, arg.n)
            # elseif isa(arg, SSAValue) # and similarly for SSAValues
            #     #println("adding ", arg.id, " to TaintedPC of ", stmt_lattice)
            #     addTaint!(stmt_lattice, arg.id, nothing)
            # end # if its not an Argument or SSAValue, we don't care
        end
    end
    return new_state
end

function merge_state_stmt!(state::TaintState, stmt, pc::Int)
    stmt_lattice = state.ssavalues[pc]
    if !stmt_lattice.Analyzed
        stmt_lattice.Analyzed = true
    end
    if isdefined(stmt, :args)
        for arg in stmt.args
            maybeAddTaint!(stmt_lattice, arg)
            # if isa(arg, Argument) # if an Argument is in the arguments of this stmt, consider this stmt tainted by that Argument
            #     addTaint!(stmt_lattice, nothing, arg.n)
            # elseif isa(arg, SSAValue) # and similarly for SSAValues
            #     addTaint!(stmt_lattice, arg.id, nothing)
            # end # if its not an Argument or SSAValue, we don't care
        end
    elseif isdefined(stmt, :val)
        val = stmt.val
        maybeAddTaint!(stmt_lattice, val)
    end
    state.ssavalues[pc] = stmt_lattice
    return state
end


# return the ssavalues or arguments that directly taint the ssavalue at pc 
ssas_that_taint(state::TaintState, pc) = state.ssavalues[pc].TaintedPC
args_that_taint(state::TaintState, pc) = state.ssavalues[pc].TaintedArg

# adds to state.ssavalues[pc].TaintedPC and .TaintedArg the ssavalues and arguments
# that either directly or indirectly taint that pc
# TODO: Infinite loop
function propagate_taint!(state::TaintState, pc)
    ele = state.ssavalues[pc]
    new_ssas = BitSet()
    new_args = BitSet()
    done = false
    while !done
        for ssa in ele.TaintedPC
            push!(new_ssas, ssas_that_taint(state, ssa))
            push!(new_args, args_that_taint(state, ssa))
        end
        new_ele = TaintLattice(ele, new_ssas, new_args)
        if new_ele == ele
            done = true
        else
            ele = new_ele
        end
    end
    return ele
end

# gets ssavalues that this ssavalue or argument directly taints
function find_related(ssavals::Vector{TaintLattice}, val)
    related = BitSet()
    if isa(val, SSAValue)
        val = val.id
        for (idx, ele) in enumerate(ssavals)
            if arg in ele.TaintedPC
                push!(related, idx)
            end
        end
    elseif isa(val, Argument)
        val = val.n
        for (idx, ele) in enumerate(ssavals)
            if arg in ele.TaintedArg
                push!(related, idx)
            end
        end
    end
    return related
end

function retrace_taint(res::TaintState, val) # call with ssavalue or argument
    linears = BitSet()
    nonlinears = Dict{Int, BitSet}()
    # linearly related
    linears = find_related(res.ssavalues, val)

    # nonlinearly related (1 level)
    for pc in linears
        nonlinears[pc] = tainted_by(res, pc)
    end
    # nonlinearly related (n levels)
    #next_nonlinears = copy(nonlinears)
    for i in keys(nonlinears)
        for ssaval in nonlinears[i]
            ssaval_taints = tainted_by(res, ssaval)
            for tainted in ssaval_taints
                push!(nonlinears[i], tainted)
            end
            #union!(nonlinears[i], tainted_by(res, ssaval))
        end
    end
    #     if nonlinears == next_nonlinears
    #         fully_traced = true
    #     else
    #         println("Loop count: ", loops)
    #         next_nonlinears = copy(nonlinears)
    #     end
    # end

    return (linears, nonlinears)
end

const state_cache = Dict{Int, TaintState}()
has_cached_state(pc::Int) = haskey(state_cache, pc)
clear_local_cache!() = empty!(state_cache)
function cache_cleanup(cache, returns) #only keep the states that correspond to the end of a control flow branch (i.e., the states at pcs that are returns)
    #println("cache size before cleanup: ", length(cache))
    new_cache = Dict{Int, TaintState}()
    for return_idx in returns
        new_cache[return_idx] = cache[return_idx]
    end
    return new_cache
end

function propagate_cache!(cache)
    for pc in keys(cache)
        #println(pc)
        propagate_taint!(cache[pc], pc)
    end
end

# we preserve `IRCode` as well just for debugging purpose
const GLOBAL_TAINT_CACHE = IdDict{MethodInstance,Tuple{TaintState,IRCode}}()
__clear_escape_cache!() = empty!(GLOBAL_TAINT_CACHE)

const Change  = Pair{Union{Argument,SSAValue},TaintState}
const Changes = Vector{Change}

function find_taints(ir::IRCode, nargs::Int)
    clear_local_cache!()
    (; stmts) = ir
    nstmts = length(stmts)
    state = TaintState(nstmts, nargs)
    state_cache[1] = state
    #changes = Changes() # stashes changes that happen at current statement
    array_elements = Vector{Integer}() # TODO: BitSets
    returns = Vector{Integer}()

    # while true
    #     local anyupdate = false

        for pc in 1:nstmts
            stmt = stmts.inst[pc]
            if has_cached_state(pc)
                #state = TaintState(state_cache[pc], stmt, pc)
                state = merge_state_stmt!(state_cache[pc], stmt, pc)
            else
                #println("test, cache miss!")
                merge_state_stmt!(state, stmt, pc)
                state_cache[pc] = state
                #state = TaintState(state, stmt, pc)
            end

            # propagate states according to control flow
            # TODO: mark the condition ssas to determine control flow if given a constant argument in some caller
            if isa(stmt, GotoNode) 
                dest_pc = stmt.label
                state_cache[dest_pc] = state
            elseif isa(stmt, GotoIfNot)
                dest_pc = stmt.dest
                state_cache[dest_pc] = state
                state_cache[pc + 1] = state
            elseif !has_cached_state(pc + 1)
                state_cache[pc + 1] = state
            end

            # we escape statements with the `ThrownEscape` property using the effect-freeness
            # information computed by the inliner
            # is_effect_free = stmts.flag[pc] & IR_FLAG_EFFECT_FREE ≠ 0

            # collect escape information
            if isa(stmt, Expr)
                head = stmt.head
                if head === :call

                elseif head === :invoke # TODO: Use taint info from previously processed method IRs in GLOBAL_TAINT_CACHE

                elseif head === :new || head === :splatnew

                elseif head === :(=)

                elseif head === :foreigncall

                elseif head === :throw_undef_if_not # XXX when is this expression inserted ?

                elseif is_meta_expr_head(head)
                    # meta expressions doesn't account for any usages
                    continue
                elseif head === :static_parameter
                    # :static_parameter refers any of static parameters, but since they exist
                    # statically, we're really not interested in their escapes
                    continue
                elseif head === :copyast
                    # copyast simply copies a surface syntax AST, and should never use any of arguments or SSA values
                    continue
                elseif head === :undefcheck
                    # undefcheck is temporarily inserted by compiler
                    # it will be processd be later pass so it won't change any of escape states
                    continue
                elseif head === :the_exception
                    # we don't propagate escape information on exceptions via this expression, but rather
                    # use a dedicated lattice property `ThrownEscape`
                    continue
                elseif head === :isdefined
                    # just returns `Bool`, nothing accounts for any usages
                    continue
                elseif head === :enter || head === :leave || head === :pop_exception
                    # these exception frame managements doesn't account for any usages
                    # we can just ignore escape information from
                    continue
                elseif head === :gc_preserve_begin || head === :gc_preserve_end
                    # `GC.@preserve` may "use" arbitrary values, but we can just ignore the escape information
                    # imposed on `GC.@preserve` expressions since they're supposed to never be used elsewhere
                    continue
                else
                    continue
                end
            elseif isa(stmt, GlobalRef) # global load

            elseif isa(stmt, PiNode)
            elseif isa(stmt, PhiNode)
            elseif isa(stmt, PhiCNode)
            elseif isa(stmt, UpsilonNode)
            elseif isa(stmt, ReturnNode)
                push!(returns, pc)
            elseif isa(stmt, GotoNode)
            else
                #continue
            end
            # isempty(changes) && continue

            # anyupdate |= propagate_changes!(state, changes)

            # empty!(changes)
        end

    #     anyupdate || break
    # end
    #@eval Main (state_cache = $state_cache; returns = $returns)
    clean_cache = cache_cleanup(state_cache, returns)
    println("cache after cleanup: ", state_cache)
    propagate_cache!(clean_cache)
    return (state, clean_cache)
end

# # propagate changes, and check convergence
# function propagate_changes!(state::EscapeState, changes::Changes)
#     local anychanged = false

#     for (x, info) in changes
#         if isa(x, Argument)
#             old = state.arguments[x.n]
#             new = old ⊔ info
#             if old ≠ new
#                 state.arguments[x.n] = new
#                 anychanged |= true
#             end
#         else
#             x = x::SSAValue
#             old = state.ssavalues[x.id]
#             new = old ⊔ info
#             if old ≠ new
#                 state.ssavalues[x.id] = new
#                 anychanged |= true
#             end
#         end
#     end

#     return anychanged
# end

# function add_change!(@nospecialize(x), ir::IRCode, info::EscapeLattice, changes::Changes)
#     if isa(x, Argument) || isa(x, SSAValue)
#         if !isbitstype(widenconst(argextype(x, ir, ir.sptypes, ir.argtypes)))
#             push!(changes, Change(x, info))
#         end
#     end
# end

# function escape_backedges!(ir::IRCode, pc::Int, backedges::Vector{Any},
#                            state::EscapeState, changes::Changes)
#     info = state.ssavalues[pc]
#     for i in 1:length(backedges)
#         if isassigned(backedges, i)
#             add_change!(backedges[i], ir, info, changes)
#         end
#     end
# end

# function escape_call!(ir::IRCode, pc::Int, args::Vector{Any},
#                       state::EscapeState, changes::Changes)
#     ft = argextype(first(args), ir, ir.sptypes, ir.argtypes)
#     f = singleton_type(ft)
#     if isa(f, Core.IntrinsicFunction)
#         return false # COMBAK we may break soundness here, e.g. `pointerref`
#     end
#     result = escape_builtin!(f, ir, pc, args, state, changes)
#     if result === false
#         return false # nothing to propagate
#     elseif result === missing
#         # if this call hasn't been handled by any of pre-defined handlers,
#         # we escape this call conservatively
#         for i in 2:length(args)
#             add_change!(args[i], ir, AllEscape(), changes)
#         end
#         return true
#     else
#         return true
#     end
# end

# function escape_invoke!(ir::IRCode, pc::Int, args::Vector{Any},
#                         state::EscapeState, changes::Changes)
#     linfo = first(args)::MethodInstance
#     cache = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
#     args = args[2:end]
#     if isnothing(cache)
#         for x in args
#             add_change!(x, ir, AllEscape(), changes)
#         end
#     else
#         @eval Main (ir = $ir; linfo = $linfo; cache = $cache)
#         (linfostate, _ #=ir::IRCode=#) = cache
#         retinfo = state.ssavalues[pc] # escape information imposed on the call statement
#         method = linfo.def::Method
#         nargs = Int(method.nargs)
#         for i in 1:length(args)
#             arg = args[i]
#             if i ≤ nargs
#                 arginfo = linfostate.arguments[i]
#             else # handle isva signature: COMBAK will this invalid once we encode alias information ?
#                 arginfo = linfostate.arguments[nargs]
#             end
#             if isempty(arginfo.ReturnEscape)
#                 @eval Main (ir = $ir; linfo = $linfo)
#                 error("invalid escape lattice element returned from inter-procedural context: inspect `Main.ir` and `Main.linfo`")
#             end
#             info = from_interprocedural(arginfo, retinfo, pc)
#             add_change!(arg, ir, info, changes)
#         end
#     end
# end

# # reinterpret the escape information imposed on the callee argument (`arginfo`) in the
# # context of the caller frame using the escape information imposed on the return value (`retinfo`)
# function from_interprocedural(arginfo::EscapeLattice, retinfo::EscapeLattice, pc::Int)
#     @assert arginfo.ReturnEscape
#     if arginfo.ThrownEscape
#         EscapeSites = BitSet(pc)
#     else
#         EscapeSites = EMPTY_ESCAPE_SITES
#     end
#     newarginfo = EscapeLattice(true, false, arginfo.ThrownEscape, EscapeSites)
#     if arginfo.EscapeSites === ARGUMENT_ESCAPE_SITES
#         # if this is simply passed as the call argument, we can discard the `ReturnEscape`
#         # information and just propagate the other escape information
#         return newarginfo
#     else
#         # if this can be returned, we have to merge its escape information with
#         # that of the current statement
#         return newarginfo ⊔ retinfo
#     end
# end

# function escape_new!(ir::IRCode, pc::Int, args::Vector{Any},
#                      state::EscapeState, changes::Changes)
#     info = state.ssavalues[pc]
#     if info == NotAnalyzed()
#         info = NoEscape()
#         add_change!(SSAValue(pc), ir, info, changes) # we will be interested in if this allocation escapes or not
#     end

#     # propagate the escape information of this object to all its fields as well
#     # since they can be accessed through the object
#     for i in 2:length(args)
#         add_change!(args[i], ir, info, changes)
#     end
# end

# function escape_foreigncall!(ir::IRCode, pc::Int, args::Vector{Any},
#                              state::EscapeState, changes::Changes)
#     foreigncall_nargs = length((args[3])::SimpleVector)
#     name = args[1]
#     # if normalize(name) === :jl_gc_add_finalizer_th
#     #     # add `FinalizerEscape` ?
#     # end
#     add_change!(name, ir, ThrownEscape(pc), changes)
#     for i in 6:5+foreigncall_nargs
#         add_change!(args[i], ir, ThrownEscape(pc), changes)
#     end
# end

# escape_builtin!(@nospecialize(f), _...) = return missing

# # safe builtins
# escape_builtin!(::typeof(isa), _...) = return false
# escape_builtin!(::typeof(typeof), _...) = return false
# escape_builtin!(::typeof(Core.sizeof), _...) = return false
# escape_builtin!(::typeof(===), _...) = return false
# # not really safe, but `ThrownEscape` will be imposed later
# escape_builtin!(::typeof(isdefined), _...) = return false
# escape_builtin!(::typeof(throw), _...) = return false

# function escape_builtin!(::typeof(Core.ifelse), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
#     length(args) == 4 || return
#     f, cond, th, el = args
#     info = state.ssavalues[pc]
#     condt = argextype(cond, ir, ir.sptypes, ir.argtypes)
#     if isa(condt, Const) && (cond = condt.val; isa(cond, Bool))
#         if cond
#             add_change!(th, ir, info, changes)
#         else
#             add_change!(el, ir, info, changes)
#         end
#     else
#         add_change!(th, ir, info, changes)
#         add_change!(el, ir, info, changes)
#     end
# end

# function escape_builtin!(::typeof(typeassert), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
#     length(args) == 3 || return
#     f, obj, typ = args
#     info = state.ssavalues[pc]
#     add_change!(obj, ir, info, changes)
# end

# function escape_builtin!(::typeof(tuple), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
#     info = state.ssavalues[pc]
#     if info == NotAnalyzed()
#         info = NoEscape()
#     end
#     for i in 2:length(args)
#         add_change!(args[i], ir, info, changes)
#     end
# end

# function escape_builtin!(::typeof(getfield), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
#     # only propagate info when the field itself is non-bitstype
#     isbitstype(widenconst(ir.stmts.type[pc])) && return true
#     info = state.ssavalues[pc]
#     if info == NotAnalyzed()
#         info = NoEscape()
#     end
#     for i in 2:length(args)
#         add_change!(args[i], ir, info, changes)
#     end
# end

# entries
# =======

function CC.optimize(interp::TaintAnalyzer, opt::OptimizationState, params::OptimizationParams, @nospecialize(result))
    ir = run_passes_with_taint_analysis(interp, opt.src, opt)
    return CC.finish(interp, opt, params, ir, result)
end


# HACK enable copy and paste from Core.Compiler
function run_passes_with_taint_analysis end
#register_init_hook!() do
@eval CC begin
    function $TaintAnalysis.run_passes_with_taint_analysis(interp::$TaintAnalyzer, ci::CodeInfo, sv::OptimizationState)
        @timeit "convert"   ir = convert_to_ircode(ci, sv)
        @timeit "slot2reg"  ir = slot2reg(ir, ci, sv)
        @timeit "compact 1" ir = compact!(ir)
        @timeit "Inlining"  ir = ssa_inlining_pass!(ir, ir.linetable, sv.inlining, ci.propagate_inbounds)
        # @timeit "verify 2" verify_ir(ir)
        @timeit "compact 2" ir = compact!(ir)
        nargs = let def = sv.linfo.def
            isa(def, Method) ? Int(def.nargs) : 0
        end
        println("calling find_taints on ir: ")
        println(ir.stmts.inst)
        println("\n method name: ", sv.linfo.def.name)
        @timeit "collect escape information" state = $find_taints(ir, nargs)
        cache_local_state = state |> first
        cacheir = copy(ir)
        # cache this result
        $setindex!($GLOBAL_TAINT_CACHE, (cache_local_state, cacheir), sv.linfo)
        @eval Main (glob_cache = $GLOBAL_TAINT_CACHE)
        # return back the result
        interp.ir = cacheir
        interp.state = cache_local_state
        interp.linfo = sv.linfo
        @timeit "SROA"      ir = sroa_pass!(ir)
        @timeit "ADCE"      ir = adce_pass!(ir)
        @timeit "type lift" ir = type_lift_pass!(ir)
        @timeit "compact 3" ir = compact!(ir)
        if JLOptions().debug_level == 2
            @timeit "verify 3" (verify_ir(ir); verify_linetable(ir.linetable))
        end
        return ir
    end
end
#end # register_init_hook!() do

macro analyze_taints(ex0...)
    return InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :analyze_taints, ex0)
end

function analyze_taints(@nospecialize(f), @nospecialize(types=Tuple{});
                         world = get_world_counter(),
                         interp = Core.Compiler.NativeInterpreter(world))
    interp = TaintAnalyzer(interp)
    results = code_typed(f, types; optimize=true, world, interp) |> only |> first
    # @eval Main (ci = $ci)
    # res = find_taints(ci, nargs)
    # final_state = res |> first
    # for input_arg in 1:nargs
    #     (linear, nonlinear) = retrace_taint(final_state, input_arg + 1)
    #     println("argument ", input_arg + 1, " linearly taints the following variables: ", linear, "\n and nonlinearly taints the following variables: ", nonlinear)
    # end
    return (results, interp.ir, interp.state)
    #isone(length(results)) || throw(ArgumentError("`analyze_escapes` only supports single analysis result"))
    #return interp.state
    #return EscapeResult(interp.ir, interp.state, interp.linfo)
end

# utilities
# =========

# in order to run a whole analysis from ground zero (e.g. for benchmarking, etc.)
# __clear_caches!() = (__clear_code_cache!(); __clear_escape_cache!())

# function get_name_color(x::EscapeLattice, symbol::Bool = false)
#     getname(x) = string(nameof(x))
#     if x == NotAnalyzed()
#         name, color = (getname(NotAnalyzed), '◌'), :plain
#     elseif x == NoEscape()
#         name, color = (getname(NoEscape), '✓'), :green
#     elseif NoEscape() ⊏ x ⊑ AllReturnEscape()
#         name, color = (getname(ReturnEscape), '↑'), :cyan
#     elseif NoEscape() ⊏ x ⊑ AllThrownEscape()
#         name, color = (getname(ThrownEscape), '↓'), :yellow
#     elseif x == AllEscape()
#         name, color = (getname(AllEscape), 'X'), :red
#     else
#         name, color = (nothing, '*'), :red
#     end
#     return (symbol ? last(name) : first(name), color)
# end

# # pcs = sprint(show, collect(x.EscapeSites); context=:limit=>true)
# function Base.show(io::IO, x::EscapeLattice)
#     name, color = get_name_color(x)
#     if isnothing(name)
#         Base.@invoke show(io::IO, x::Any)
#     else
#         printstyled(io, name; color)
#     end
# end
# function Base.show(io::IO, ::MIME"application/prs.juno.inline", x::EscapeLattice)
#     name, color = get_name_color(x)
#     if isnothing(name)
#         return x # use fancy tree-view
#     else
#         printstyled(io, name; color)
#     end
# end

# struct EscapeResult
#     ir::IRCode
#     state::EscapeState
#     linfo::Union{Nothing,MethodInstance}
#     EscapeResult(ir::IRCode, state::EscapeState, linfo::Union{Nothing,MethodInstance} = nothing) =
#         new(ir, state, linfo)
# end
# Base.show(io::IO, result::EscapeResult) = print_with_info(io, result.ir, result.state, result.linfo)
# @eval Base.iterate(res::EscapeResult, state=1) =
#     return state > $(fieldcount(EscapeResult)) ? nothing : (getfield(res, state), state+1)

# # adapted from https://github.com/JuliaDebug/LoweredCodeUtils.jl/blob/4612349432447e868cf9285f647108f43bd0a11c/src/codeedges.jl#L881-L897
# function print_with_info(io::IO,
#     ir::IRCode, (; arguments, ssavalues)::EscapeState, linfo::Union{Nothing,MethodInstance})
#     # print escape information on SSA values
#     function preprint(io::IO)
#         ft = ir.argtypes[1]
#         f = singleton_type(ft)
#         if f === nothing
#             f = widenconst(ft)
#         end
#         print(io, f, '(')
#         for (i, arg) in enumerate(arguments)
#             i == 1 && continue
#             c, color = get_name_color(arg, true)
#             printstyled(io, '_', i, "::", ir.argtypes[i], ' ', c; color)
#             i ≠ length(arguments) && print(io, ", ")
#         end
#         print(io, ')')
#         if !isnothing(linfo)
#             def = linfo.def
#             printstyled(io, " in ", (isa(def, Module) ? (def,) : (def.module, " at ", def.file, ':', def.line))...; color=:bold)
#         end
#         println(io)
#     end

#     # print escape information on SSA values
#     # nd = ndigits(length(ssavalues))
#     function preprint(io::IO, idx::Int)
#         c, color = get_name_color(ssavalues[idx], true)
#         # printstyled(io, lpad(idx, nd), ' ', c, ' '; color)
#         printstyled(io, c, ' '; color)
#     end

#     print_with_info(preprint, (args...)->nothing, io, ir)
# end

# function print_with_info(preprint, postprint, io::IO, ir::IRCode)
#     io = IOContext(io, :displaysize=>displaysize(io))
#     used = Base.IRShow.stmts_used(io, ir)
#     # line_info_preprinter = Base.IRShow.lineinfo_disabled
#     line_info_preprinter = function (io::IO, indent::String, idx::Int)
#         r = Base.IRShow.inline_linfo_printer(ir)(io, indent, idx)
#         idx ≠ 0 && preprint(io, idx)
#         return r
#     end
#     line_info_postprinter = Base.IRShow.default_expr_type_printer
#     preprint(io)
#     bb_idx_prev = bb_idx = 1
#     for idx = 1:length(ir.stmts)
#         preprint(io, idx)
#         bb_idx = Base.IRShow.show_ir_stmt(io, ir, idx, line_info_preprinter, line_info_postprinter, used, ir.cfg, bb_idx)
#         postprint(io, idx, bb_idx != bb_idx_prev)
#         bb_idx_prev = bb_idx
#     end
#     max_bb_idx_size = ndigits(length(ir.cfg.blocks))
#     line_info_preprinter(io, " "^(max_bb_idx_size + 2), 0)
#     postprint(io)
#     return nothing
# end

end # module TaintAnalysis
