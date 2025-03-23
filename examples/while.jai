main :: () {
    // plain_while();
    // double_yield();
    // yield_end_of_block();
    nested_while();
    // if_in_while();
}

// plain_while :: () {
//     whiles :: () -> s64 {
//         local:= 0;
//         while local < 2 {
//             local += 1;
//         }
//         local += 9;
//         return local;
//     }

//     yielding := init(#run,stallable into_yielding(whiles));
//     status, result := next(*yielding);
//     assert(status == .RETURN && result == 11, "plain while return: %\n", result);
// }

// double_yield :: () {
//     whiles :: () -> s64 {
//         local:= 0;
//         while local < 4 {
//             yield(local);
//             local += 1;
//             yield(local);
//             local += 2;
//         }
//         local += 9;
//         return local;
//     }

//     yielding := init(#run,stallable into_yielding(whiles));
//     status, result := next(*yielding);
//     assert(status == .YIELD && result == 0, "double yield: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .YIELD && result == 1, "double yield: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .YIELD && result == 3, "double yield: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .YIELD && result == 4, "double yield: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .RETURN && result == 15, "double yield return %\n", result);
// }

// yield_end_of_block :: () {
//     whiles :: () -> s64 {
//         local:= 0;
//         while local < 1 {
//             local += 1;
//             yield(local);
//         }
//         local += 9;
//         return local;
//     }

//     yielding := init(#run,stallable into_yielding(whiles));
//     status, result := next(*yielding);
//     assert(status == .YIELD && result == 1, "while end yield: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .RETURN && result == 10, "while end yield return: %\n", result);
// }

nested_while :: () {
    whiles :: () -> s64 {
        local:= 0;
        {
            while local < 2 {
                nested:= 1;
                {
                    while nested < 2 {
                        local += 2;
                        {
                            yield(nested);
                        }
                        nested += 1;
                    }
                }
                yield(local);
            }
        }
        local += 9;
        return local;
    }

    yielding := init(#run,stallable into_yielding(whiles));
    status, result := next(*yielding);
    assert(status == .YIELD && result == 1, "nested while: %\n", result);
    status, result  = next(*yielding);
    assert(status == .YIELD && result == 2, "nested while: %\n", result);
    status, result  = next(*yielding);
    assert(status == .RETURN && result == 11, "nested while return: %\n", result);
}

// if_in_while :: () {
//     whiles :: () -> s64 {
//         local:= 0;
//         while local < 4 {
//             if local % 2 == 0 {
//                 local += 4;
//                 yield(local);
//             } else {
//                 yield(local);
//             }
//             local -= 1;
//         }
//         local += 9;
//         return local;
//     }

//     yielding := init(#run,stallable into_yielding(whiles));
//     status, result := next(*yielding);
//     assert(status == .YIELD && result == 4, "if in while: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .YIELD && result == 3, "if in while: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .YIELD && result == 6, "if in while: %\n", result);
//     status, result  = next(*yielding);
//     assert(status == .RETURN && result == 14, "if in while return: %\n", result);
// }


#scope_file
#import,file "../module.jai";
#import "Basic";
