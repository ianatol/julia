let
    m = Module()
    @eval m begin
        foo(a::Val{1}) = 1
        foo(a::Val{2}) = 2
        foo(a::Val{3}) = 3
        foo(a::Val{4}) = undefvar
    end

    # run first analysis and cache
    result = @eval m $analyze_call((Int,)) do a
        foo(Val(a))
    end
end