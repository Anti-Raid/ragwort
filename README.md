# Ragwort

A (fairly) simple GC'd scheme-like language for defining Discord bots etc. in AntiRaid. Replaces luau/luwu and is *way* easier to parse (for use in the website etc.) and generate code for. May be potentially faster too (and is probably more secure too compared to Luau/Luwu).

## Memory Cages

To avoid memory safety issues with ragwort, ragwort includes a 'memory cage' in which ragwort heap allocated memory is allocated in a 64MB (configurable) virtual memory cage. This means that corruption of the memory cage cannot directly threaten the actual integrity of the underlying host unless a sandbox escape is found.

## GC

See ``src/gc`` folder for implementation of ragworts GC. Internally uses a incremental tristate mark-sweep gc with generations (because scheme code tends to be full of short-lived allocations so most objects will likely fall into young generation)

## Stack

ragwort uses a segmented stack model to model its stack frames. This enables for fast ``call/cc`` by splitting the segmented stack (record `(segment, start, end)` in continuation and GC `(end top)` internally when continuation ends).

## Dependencies

- `syn`
- `memmap2` (gc memory cage)
- `libc` (gc memory cage)