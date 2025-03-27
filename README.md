Compact representation of UTF-8 Strings that are immutable and less than 256 bytes in length.

## About
`CompactString` is a more memory efficient string type for situations where you need to store a string that:
- is immutable
- is less than 256 bytes in length

The benefit of `CompactString` over `String` is that it contains less memory overhead, making it ideal for
memory critical applications.


## Motivation
Many memory critical applications benefit from string types that are more compact in memory.
Most of the existing memory optimized string crates rely on small string optimization, which store up to 24 bytes on
the stack for small strings, and heap allocate for longer strings. This means that:

1. All strings are at least 24 bytes in total size.
2. No memory reduction for strings longer than 24.

The advantage of `CompactString` is that it only takes up 9 bytes of memory overhead, saving 15 bytes of overhead
for each string stored in the application.


## Design
CompactString will only store a 8 bytes raw pointer on the stack.
It points to a contiguous u8 memory block with size = length + 1,
where the first entry of the memory block represents the length of the string,
and string data follows.

```text
                               +------+-------+
CompactString                  | index| value |
+-----+-----+                  +------+-------+
| ptr | xxx +----------------->|  0   |   5   |
+-----+-----+                  +------+-------+
                               |  1   |   h   |
                               +------+-------+
                               |  2   |   e   |
                               +------+-------+
                               |  3   |   l   |
                               +------+-------+
                               |  4   |   l   |
                               +------+-------+
                               |  5   |   o   |
                               +------+-------+
```

The decision of storing length on heap is to avoid the rounded overhead due to 8 bytes alignment from the pointer.
If we store the length on stack, the stack size of struct would be 16 bytes after alignment.

With the new compact string design, string overhead is cut from 24 bytes down to 9 bytes.
Immutability is checked by keeping the pointer private and not exposing functions to mutate the string.


## Performance
It doesn't aim to be more performant than `String` in the general case. For most of the string operations,
`CompactString` performance is comparable to or slightly worse than that of `String`. There is a computation overhead
on `from_utf8` operation, which user may expect 50% increase in computation time.