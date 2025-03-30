main :: () {
    yield_in_expand();
    return_in_expand();
}

yield_in_expand :: () {
    expands :: () -> s64 {
        macy :: () #expand {
            `yield(`local);
            {
                `guy := 17;
            }
        }
        local := 0;
        {
            defer local += 1;
            local += 2;
            macy();
            yield(guy);
        }
        return local;
    }

    yielding := init(#run,stallable into_yielding(expands));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 2, "yield_in_expand: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 17, "yield_in_expand: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 3, "yield_in_expand return: %\n", result);
}

return_in_expand :: () {
    expands :: () -> s64 {
        macy :: () #expand {
            `local += 4;
            `return(`local);
        }
        local := 0;
        if local < 2    {
            macy();
        }
        return local;
    }

    yielding := init(#run,stallable into_yielding(expands));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 4, "return_in_expand return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
