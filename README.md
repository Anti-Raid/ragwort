# Ragwort

A (fairly) simple GC'd scheme-like language for defining Discord bots etc. in AntiRaid. Replaces luau/luwu and is *way* easier to parse (for use in the website etc.) and generate code for. May be potentially faster too (and is probably more secure too compared to Luau/Luwu).

## Command line

``crates/cli`` builds the ``ragwort`` command:

- ``ragwort [name=folder]... entry.rg`` runs a file. ``name=folder`` makes the files in ``folder`` the module ``name``, which code gets with ``(require name)``; ``=folder`` names the module as the folder.
- ``ragwort [name=folder]...`` opens a REPL, which prints the value of each form.
- ``ragwort compile [name=folder]... [entry.rg]`` compiles the modules and the entry point and prints their bytecode. The modules run, since code is compiled against what the modules it requires define; the entry point doesn't.

A ``.rg`` file is Scheme and a ``.rgn`` file is native ragwort. ``(require repl)`` gives ``display``, ``write`` and ``newline``.

## Memory Safety

ragwort's heap is a 64MB region of 64-bit words, and every reference into it is an index, so the GC and everything built on it are safe Rust. The only unsafe code is in ``crates/gc-region``, which maps the region and gives free pages back to the system. A bug in the GC or a corrupted object gives wrong results or a panic, never memory corruption in the host.

## GC

See ``crates/types/src/gc`` for ragwort's GC. Internally uses a incremental tristate mark-sweep gc with generations (because scheme code tends to be full of short-lived allocations so most objects will likely fall into young generation), and evacuates fragmented pages.

## Stack

ragwort uses a segmented stack model to model its stack frames. This enables for fast ``call/cc`` by splitting the segmented stack (record `(segment, start, end)` in continuation and GC `(end top)` internally when continuation ends).

## Dependencies

- `syn`
- `memmap2` (gc region)
- `libc` (gc region)