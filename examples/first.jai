main :: () {
    return_only();
    yield_constantly();
    basic_state_machine();
    locals();
}

return_only :: () {
    empty :: () -> s64 {
        return 3;
    }
    // compty :: (self: *Coroutine(void, s64)) -> Co_Status, s64 {
    //     return .RETURN, 3;
    // }

    YieldProc :: #run, stallable into_yielding(code_of(empty));
    yielding := init(YieldProc);
    empty_calls := 0;
    for yielding {
        empty_calls += 1;
        print("empty: %\n", it);
    }
    assert(empty_calls == 1);
}

yield_constantly :: () {
    always :: () -> s64 {
        yield(15);
    }
    // coways :: (self: *Coroutine(void, s64)) -> Co_Status, s64 {
    //     return .YIELD, 15;
    // }

    YieldProc :: #run, stallable into_yielding(code_of(always));
    yielding := init(YieldProc);
    for yielding {
        print("always 15: %\n", it);
        assert(it == 15);
        if it_index > 3 then break;
    }
}

basic_state_machine :: () {
    stating :: () -> s64 {
        yield(5);
        return 17;
    }
    // costating :: (self: *COROUTINE) -> status: Co_Status, s64 {
    //     if self.position == {
    //     case 0;
    //         self.position = 1;
    //         return .YIELD, 5;
    //     case 1;
    //         self.position = 0;
    //         return .RETURN, 17;
    //     }
    // }
    YieldProc :: #run,stallable into_yielding(code_of(stating));
    yielding := init(YieldProc);

    status, result := next(*yielding);
    print("state yield : %\n", result);
    assert(status == .YIELD && result == 5);

    status, result  = next(*yielding);
    print("state return: %\n", result);
    assert(status == .RETURN && result == 17);
}

locals :: () {
    stating :: () -> s64 {
        local:= 42;
        yield(local);
        local += 1;
        return local;
    }
    // colocal :: (self: *COROUTINE) -> status: Co_Status, s64 {
    //     if self.position == {
    //     case 0;
    //         self.state.local = 42;
    //         self.position = 1;
    //         return .YIELD, self.local;
    //     case 1;
    //         self.state.local += 1;
    //         self.position = 0;
    //         return .RETURN, self.local;
    //     }
    // }
    YieldProc :: #run,stallable into_yielding(code_of(stating));
    yielding := init(YieldProc);

    status, result := next(*yielding);
    print("local yield : %\n", result);
    assert(status == .YIELD && result == 42);

    status, result  = next(*yielding);
    print("local return: %\n", result);
    assert(status == .RETURN && result == 43);
}

#scope_file
#import,file "../module.jai";
#import "Basic";
