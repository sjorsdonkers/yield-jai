main :: () {
    constant_after_yield();
    constant_from_parent_constant();
    constant_code();
}

constant_after_yield :: () {
    constants :: () -> s64 {
        constant :: 3;
        yield(constant+1);
        return constant+2;
    }

    yielding := init(#run,stallable into_yielding(constants));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 4, "constant after yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 5, "constant after yield return: %\n", result);
}

constant_from_parent_constant :: () {
    constants :: () -> s64 {
        CONSTANT :: 3;
        {
            NESTED :: CONSTANT + 6;
            yield(NESTED-1);
        }
        return CONSTANT+2;
    }

    yielding := init(#run,stallable into_yielding(constants));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 8, "constant from parent constant: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 5, "constant from parent constant return: %\n", result);
}

constant_code :: () {
    constants :: () -> s64 {
        CODE :: #code 3;

        return -1 + #insert CODE;
    }

    yielding := init(#run,stallable into_yielding(constants));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 2, "constant code return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
