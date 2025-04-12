main :: () {
    yield_in_expand();
    return_in_expand();
    expand_with_param();
    expand_with_default_param();
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

expand_with_param :: () {
    expands :: () -> s64 {
        macy :: (arg: s64) #expand {
            `yield(`local + arg);
            {
                `guy := 17 - arg;
            }
        }
        local := 0;
        {
            defer local += 1;
            local += 2;
            macy(3);
            yield(guy);
        }
        return local;
    }

    yielding := init(#run,stallable into_yielding(expands));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 5, "yield_in_expand: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 14, "yield_in_expand: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 3, "yield_in_expand return: %\n", result);
}

expand_with_default_param :: () {
    expands :: () -> s64 {
        macy :: (arg1: s64, arg2:=6) #expand {
            `yield(`local + arg1);
            {
                `guy := 17 - arg2;
            }
        }
        local := 0;
        {
            defer local += 1;
            local += 2;
            macy(7);
            yield(guy);
        }
        return local;
    }

    yielding := init(#run,stallable into_yielding(expands));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 9, "yield_in_expand: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 11, "yield_in_expand: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 3, "yield_in_expand return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
