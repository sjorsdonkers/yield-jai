main :: () {
    // plain_for();
    // yield_in_for();
    // rename_it();
    expanding_for();
}

// plain_for :: () {
//     fors :: () -> s64 {
//         local:= 0;
//         for 0..1 {
//             local += 1;
//         }
//         local += 9;
//         return local;
//     }

//     yielding := init(#run,stallable into_yielding(fors));
//     status, result := next(*yielding);
//     assert(status == .RETURN && result == 11, "plain for return: %\n", result);
// }

// yield_in_for :: () {
//     fors :: () -> s64 {
//         local:= 0;
//         for 0..1 {
//             defer local += 2;
//             local += 1;
//             yield(local);
//         }
//         local += 9;
//         return local;
//     }

//     // local = 0;
//     // {
//     //     it := 0;
//     //     while it <= 1{
//     //         defer it += 1;
//     //         yield(local);
//     //         local += 1;
//     //     }
//     // }

//     yielding := init(#run,stallable into_yielding(fors));
//     status, result := next(*yielding);
//     assert(status == .YIELD && result == 1, "yield_in_for: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .YIELD && result == 4, "yield_in_for: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .RETURN && result == 15, "yield_in_for return: %\n", result);
// }

// rename_it :: () {
//     fors :: () -> s64 {
//         local:= 0;
//         for myt: 0..1 {
//             defer local += 2;
//             local += myt;
//             yield(local);
//         }
//         local += 9;
//         return local;
//     }

//     yielding := init(#run,stallable into_yielding(fors));
//     status, result := next(*yielding);
//     assert(status == .YIELD && result == 0, "rename_it: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .YIELD && result == 3, "rename_it: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .RETURN && result == 14, "rename_it return: %\n", result);
// }

expanding_for :: () {
    // The plan
    // Add optional member to Process_Block, Rename in the insert directive, block

    ////////// Why are al set positions 0
    fors :: () -> s64 {
        local: Holder;
        array_add(*local.values, 6, 8);
        for local {
            yield(it);
        }
        return 9;
    }

    yielding := init(#run,stallable into_yielding(fors));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 6, "expanding_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 8, "expanding_for: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 9, "expanding_for return: %\n", result);
}

Holder :: struct {
    values: [..]s64;
}
for_expansion :: (holder: Holder, body: Code, flags: For_Flags) #expand {
    for slot: 0..holder.values.count-1 {
        `it_index := slot;
        a := 99;
        `it := holder.values[slot];
        #insert body;
    }
}
#poke_name Coro Holder;

#scope_file
using Coro :: #import,file "../module.jai";
#import "Basic";
