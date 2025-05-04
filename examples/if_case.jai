main :: () {
    plain_if_case();
    yield_or_not();

}

plain_if_case :: () {
    ifs :: () -> s64 {
        local:= 2;
        if local == {
        case 0; local += 1;
        case 1; local += 2;
        case 2; local += 3;
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(ifs));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 14, "plain if case return: %\n", result);
}

yield_or_not :: () {
    ifs :: (arg: s64) -> s64 {
        if arg == {
        case 1;
            arg += 2;
            yield(arg);
            #through;
        case 2; arg += 3;
        case 3; arg += 4;
        }
        arg += 9;
        return arg;
    }

    yielding := init(#run,stallable into_yielding(ifs));
    yielding.arguments.arg = 1;
    status, result := next(*yielding);
    assert(status == .YIELD && result == 3, "yield or not yield: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 15, "yield or not return: %\n", result);

    yielding.arguments.arg = 3;
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 16, "yield or not return: %\n", result);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
