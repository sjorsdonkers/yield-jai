// TODO store the initial arguments in the coroutine state set from init call
// Eventually a proc transformed to yielding or have yield statements remove should have the same effect when executed till completion.
// If yield is placed in a spot that does not support it, it will not compile, for example in the condition of an if statement.
// As implementation continues, more locations will be supported.

main :: () {
    return_only();
    yield_constantly();
    basic_state_machine();
    locals();
    nested_block();
    if_statement();
}

return_only :: () {
    empty :: () -> s64 {
        return 3;
    }
    // co_empty :: (self: *Coroutine(void, s64)) -> Co_Status, s64 {
    //     return .RETURN, 3;
    // }

    YieldProc :: #run,stallable into_yielding(empty);
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
    // co_always :: (self: *Coroutine(void, s64)) -> Co_Status, s64 {
    //     return .YIELD, 15;
    // }

    YieldProc :: #run,stallable into_yielding(always);
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
    // co_stating :: (self: *COROUTINE) -> status: Co_Status, s64 {
    //     if self.position == {
    //     case 0;
    //         self.position = 1;
    //         return .YIELD, 5;
    //     case 1;
    //         self.position = 0;
    //         return .RETURN, 17;
    //     }
    // }
    YieldProc :: #run,stallable into_yielding(stating);
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
    // co_stating :: (self: *COROUTINE) -> status: Co_Status, s64 {
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
    YieldProc :: #run,stallable into_yielding(stating);
    yielding := init(YieldProc);

    status, result := next(*yielding);
    print("local yield : %\n", result);
    assert(status == .YIELD && result == 42);

    status, result  = next(*yielding);
    print("local return: %\n", result);
    assert(status == .RETURN && result == 43);
}

nested_block :: () {
    block :: () -> s64 {
        local:= 42;
        {
            local += 2;
            {
                other := 1;
                yield(local);
                local += other;
            }
        }
        return local;
    }
    // State :: struct {
    //     local: s64;
    //     block_1: struct {
    //         block_1: struct {
    //             other: s64;
    //         };
    //     };
    // }

    // co_block :: (self: *COROUTINE) -> status: Co_Status, s64 {
    //     using self.state;
    //     if self.position == {
    //     case 0;
    //         local = 42;
    //         {
    //             using block_1;
    //             local += 2;
    //             {
    //                 using block_1;
    //                 other = 1;
    //                 self.position = 1;
    //                 return .YIELD, self.local;
    //             }
    //         }
    //     case 1;
    //         {
    //             using block_1;
    //             {
    //                 using block_1;
    //                 local += other;
    //             }
    //         }
    //         self.position = 0;
    //         return .RETURN, self.local;
    //     }
    // }
    YieldProc :: #run,stallable into_yielding(block);
    yielding := init(YieldProc);

    status, result := next(*yielding);
    print("nested yield : %\n", result);
    assert(status == .YIELD && result == 44);

    status, result  = next(*yielding);
    print("nested return: %\n", result);
    assert(status == .RETURN && result == 45);
}

if_statement :: () {
    ifs :: (arg: s64) -> s64 {
        local:= arg;
        if local > 15 {
            yield(local);
            local += 2;
        } else {
            local += 1;
            yield(local);
            local += 3;
        }
        local += 4;
        return local;
    }

    // (self: *COROUTINE) -> status: Co_Status, s64 {
    //     using self.state;
    //     while true if self.position == {
    //     case; self.position = 0;
    //     case 0;
    //         local = 13;
    //         if local > 15 {
    //             using then_1;
    //             self.position = 1;
    //             return .YIELD, local;
    //         } else {
    //             using else_1;
    //             local += 1;
    //             self.position = 2;
    //             return .YIELD, local;
    //         }
    //         self.position = 3;
    //     case 1;
    //         {
    //             using then_1;
    //             local += 2;
    //         }
    //         self.position = 3;
    //     case 2;
    //         {
    //             using else_1;
    //             local += 3;
    //         }
    //         self.position = 3;
    //     case 3;
    //         local += 4;
    //         self.position = 0;
    //         return .RETURN, local;
    //     }
    // }

    YieldProc :: #run,stallable into_yielding(ifs);
    yielding := init(YieldProc);
    yielding.arguments = .{13};

    status, result := next(*yielding);
    print("if yield : %\n", result);
    assert(status == .YIELD && result == 14);

    status, result  = next(*yielding);
    print("if return: %\n", result);
    assert(status == .RETURN && result == 21);

    // yielder(ifs, 13); Not used for now
}

#scope_file
#import,file "../module.jai";
#import "Basic";
