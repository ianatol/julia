# This file is a part of Julia. License is MIT: https://julialang.org/license

function inflate_ir(ci::CodeInfo, linfo::MethodInstance)
    sptypes = sptypes_from_meth_instance(linfo)
    if ci.inferred
        argtypes, _ = matching_cache_argtypes(linfo, nothing, false)
    else
        argtypes = Any[ Any for i = 1:length(ci.slotflags) ]
    end
    return inflate_ir(ci, sptypes, argtypes)
end

function inflate_ir(ci::CodeInfo, sptypes::Vector{Any}, argtypes::Vector{Any})
    code = copy_exprargs(ci.code) # TODO: this is a huge hot-spot
    cfg = compute_basic_blocks(code)
    for i = 1:length(code)
        stmt = code[i]
        # Translate statement edges to bb_edges
        if isa(stmt, GotoNode)
            code[i] = GotoNode(block_for_inst(cfg, stmt.label))
        elseif isa(stmt, GotoIfNot)
            code[i] = GotoIfNot(stmt.cond, block_for_inst(cfg, stmt.dest))
        elseif isa(stmt, PhiNode)
            code[i] = PhiNode(Int32[block_for_inst(cfg, Int(edge)) for edge in stmt.edges], stmt.values)
        elseif isa(stmt, Expr) && stmt.head === :enter
            stmt.args[1] = block_for_inst(cfg, stmt.args[1])
            code[i] = stmt
        else
            code[i] = stmt
        end
    end
    nstmts = length(code)
    ssavaluetypes = let ssavaluetypes = ci.ssavaluetypes
        ssavaluetypes isa Vector{Any} ? copy(ssavaluetypes) : Any[ Any for i = 1:(ssavaluetypes::Int) ]
    end
    stmts = InstructionStream(code, ssavaluetypes, Any[nothing for i = 1:nstmts], copy(ci.codelocs), copy(ci.ssaflags))
    ir = IRCode(stmts, cfg, collect(LineInfoNode, ci.linetable), argtypes, Any[], sptypes)
    return ir
end

function has_bad_phis(ci::CodeInfo)
    if ci.code[1] isa PhiNode
        return true
    else
        return false
    end
end

function handle_bad_phis!(ci::CodeInfo)
    # Insert goto %2
    prepend!(ci.code, [Core.GotoNode(2)])
    prepend!(ci.codelocs, 1)

    #Increment entry-block-pointing PhiNode edges
    for i = 1:length(ci.code)
        stmt = ci.code[i]
        if isa(stmt, PhiNode)
            # map(x -> x == 0 ? x + 1 : x, stmt.edges)
            for j = 1:length(stmt.edges)
                if stmt.edges[j] == 0
                    stmt.edges[j] += 1
                end
            end
            ci.code[i] = stmt
        end
    end
end

function replace_code_newstyle!(ci::CodeInfo, ir::IRCode, nargs::Int)
    @assert isempty(ir.new_nodes)
    # All but the first `nargs` slots will now be unused
    resize!(ci.slotflags, nargs)
    stmts = ir.stmts
    ci.code, ci.ssavaluetypes, ci.codelocs, ci.ssaflags, ci.linetable =
        stmts.inst, stmts.type, stmts.line, stmts.flag, ir.linetable
    for metanode in ir.meta
        push!(ci.code, metanode)
        push!(ci.codelocs, 1)
        push!(ci.ssavaluetypes::Vector{Any}, Any)
        push!(ci.ssaflags, IR_FLAG_NULL)
    end

    # Check for the rare case of PhiNodes in the entry block
    # If found, add a GoToNode with a destination of %2 in the entry block 
    # This causes the entry block to split, where the new entry block is just the new GoToNode
    # We then increment PhiNode edges that were previously pointing to the entry block

    if has_bad_phis(ci)
        handle_bad_phis!(ci)
    end

    # Translate BB Edges to statement edges
    # (and undo normalization for now)
    for i = 1:length(ci.code)
        stmt = ci.code[i]
        # if i == 1 && isa(stmt, PhiNode)
        #     throw(ErrorException("Function created problematic PhiNode"))
        # end 
        if isa(stmt, GotoNode)
            stmt = GotoNode(first(ir.cfg.blocks[stmt.label].stmts))
        elseif isa(stmt, GotoIfNot)
            stmt = GotoIfNot(stmt.cond, first(ir.cfg.blocks[stmt.dest].stmts))
        elseif isa(stmt, PhiNode)
            if 0 in stmt.edges
                # @eval Main _ci = $(ci)
                
                #Main.Base.show(ci)
            end
            stmt = PhiNode(Int32[last(ir.cfg.blocks[edge].stmts) for edge in stmt.edges], stmt.values)
        elseif isa(stmt, Expr) && stmt.head === :enter
            stmt.args[1] = first(ir.cfg.blocks[stmt.args[1]::Int].stmts)
        end
        ci.code[i] = stmt
    end
    
end

# used by some tests
inflate_ir(ci::CodeInfo) = inflate_ir(ci, Any[], Any[ Any for i = 1:length(ci.slotflags) ])
