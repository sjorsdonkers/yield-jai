main :: () {
    constant_after_yield();
    // constant_code();
    // constant_from_parent_constant();
}

constant_after_yield :: () {
    constants :: () -> s64 {
        constant :: 3;
        yield(constant+1);
        return constant+2;
    }

    yielding := init(#run,stallable into_yielding(constants));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 4, "constant after yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 5, "constant after yield return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
