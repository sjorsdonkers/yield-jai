main :: () {
    plain_if();
    plain_if_else();
    yield_or_not();
    nested_if();
}

plain_if :: () {
    ifs :: () -> s64 {
        local:= 0;
        if local < 2 {
            local += 1;
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(ifs));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 10, "plain if return: %\n", result);
}

plain_if_else :: () {
    ifs :: () -> s64 {
        local:= 2;
        if local < 2 {
            local += 1;
        } else {
            local += 2;
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(ifs));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 13, "plain if else return: %\n", result);
}

yield_or_not :: () {
    ifs :: (arg: s64) -> s64 {

        if arg < 2 {
            arg += 1;
            yield(arg);
        } else {
            arg += 2;
        }
        arg += 9;
        return arg;
    }

    yielding := init(#run,stallable into_yielding(ifs));
    yielding.arguments.arg = 1;
    status, result := next(*yielding);
    assert(status == .YIELD && result == 2, "yield or not yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 11, "yield or not return: %\n", result);

    yielding.arguments.arg = 3;
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 14, "yield or not return: %\n", result);
}

nested_if :: () {
    ifs :: (arg: s64) -> s64 {
        if arg < 2 {
            arg *= 2;
            yield(arg);
            if arg < 2 {
                arg += 1;
                yield(17);
            } else {
                arg += 2;
            }
        } else {
            arg -= 2;
            {
                if arg < 2 {
                    arg += 1;
                } else {
                    {
                        arg += 2;
                        yield(14);
                    }
                }
            }
        }
        arg += 9;
        return arg;
    }

    yielding := init(#run,stallable into_yielding(ifs));
    yielding.arguments.arg = 0;
    status, result := next(*yielding);
    assert(status == .YIELD && result == 0, "nested if: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 17, "nested if: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 10, "nested if return: %\n", result);

    yielding.arguments.arg = 1;
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 2, "nested if: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 13, "nested if return: %\n", result);

    yielding.arguments.arg = 3;
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 11, "nested if return: %\n", result);

    yielding.arguments.arg = 10;
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 14, "nested if: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 19, "nested if return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
