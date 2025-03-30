main :: () {
    plain_for();
    yield_in_for();
}

plain_for :: () {
    fors :: () -> s64 {
        local:= 0;
        for 0..1 {
            local += 1;
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 11, "plain for return: %\n", result);
}

yield_in_for :: () {
    fors :: () -> s64 {
        local:= 0;
        for 0..1 {
            defer local += 2;
            local += 1;
            yield(local);
        }
        local += 9;
        return local;
    }

    // local = 0;
    // {
    //     it := 0;
    //     while it <= 1{
    //         defer it += 1;
    //         yield(local);
    //         local += 1;
    //     }
    // }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 1, "yield_in_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 4, "yield_in_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 15, "yield_in_for return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
