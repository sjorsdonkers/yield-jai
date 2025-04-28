main :: () {
    plain_for();
    yield_in_for();
    rename_it();
    array_for();
    plain_expanding_for();
    yield_in_expanding_for();
}

plain_for :: () {
    fors :: () -> s64 {
        local:= 0;
        for 0..1 {
            local += it;
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 10, "plain for return: %\n", result);
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

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 1, "yield_in_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 4, "yield_in_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 15, "yield_in_for return: %\n", result);
}

rename_it :: () {
    fors :: () -> s64 {
        local:= 0;
        for myt: 0..1 {
            defer local += 2;
            local += myt;
            yield(local);
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 0, "rename_it: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 3, "rename_it: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 14, "rename_it return: %\n", result);
}

array_for :: () {
    fors :: () -> s64 {
        locals:= u16.[7, 4];
        for myt, my_idx: locals {
            yield(my_idx);
            yield(myt);
        }
        return 9;
    }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 0, "rename_it: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 7, "rename_it: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 1, "rename_it: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 4, "rename_it: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 9, "rename_it return: %\n", result);
}

plain_expanding_for :: () {
    fors :: () -> s64 {
        sum := 0;
        local: Holder;
        array_add(*local.values, 6, 8);
        for myt: local {
            sum += myt;
        }
        return sum;
    }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .RETURN && result == 14, "expanding_for return: %\n", result);
}

yield_in_expanding_for :: () {
    fors :: () -> s64 {
        local: Holder;
        array_add(*local.values, 6, 8);
        for myt, my_idx: local {
            yield(my_idx);
            yield(myt);
        }
        return 9;
    }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 0, "expanding_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 6, "expanding_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 1, "expanding_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 8, "expanding_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 9, "expanding_for return: %\n", result);
}

Holder :: struct {
    values: [..]u8;
}
for_expansion :: (holder: Holder, body: Code, flags: For_Flags) #expand {
    for slot: 0..holder.values.count-1 {
        `it_index := slot;
        `it := holder.values[slot];
        #insert body;
    }
}
#poke_name Coro Holder; // TODO TODO change the implementation such that all code gets inserted in the current scope

#scope_file
using Coro :: #import,file "../module.jai";
#import "Basic";
