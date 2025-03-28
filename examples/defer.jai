main :: () {
    yield_after_defer();
}

yield_after_defer :: () {
    defers :: () -> s64 {
        local := 0;
        {
            defer local += 1;
            yield(local);
            local += 2;
            yield(local);
        }
        return local;
    }

    yielding := init(#run,stallable into_yielding(defers));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 0, "yield_after_defer: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 2, "yield_after_defer: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 3, "yield_after_defer return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
