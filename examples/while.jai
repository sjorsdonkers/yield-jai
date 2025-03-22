main :: () {
    double_yield();
    yield_end_of_block();
}

double_yield :: () {
    whiles :: () -> s64 {
        local:= 0;
        while local < 4 {
            yield(local);
            local += 1;
            yield(local);
            local += 2;
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(whiles));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 0, "double yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 1, "double yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 3, "double yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 4, "double yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 15, "double yield return %\n", result);
}

yield_end_of_block :: () {
    whiles :: () -> s64 {
        local:= 0;
        while local < 1 {
            local += 1;
            yield(local);
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(whiles));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 1, "while end yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 10, "while end yield return: %\n", result);
}


#scope_file
#import,file "../module.jai";
#import "Basic";
