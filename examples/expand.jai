main :: () {
    yield_in_expand();
}

yield_in_expand :: () {
    expands :: () -> s64 {
        macy :: () #expand {
            yield(`local); // Should yield be backticked?
        }
        local := 0;
        {
            defer local += 1;
            local += 2;
            macy();
        }
        return local;
    }

    yielding := init(#run,stallable into_yielding(expands));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 2, "yield_in_expand: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 3, "yield_in_expand return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
