# Soundness

Why safe code using `ragwort-gc` can't cause undefined behavior. This is a written argument, not a machine-checked proof. Each invariant below has a short name, says what establishes it and what relies on it, and the `unsafe` code cites the names, as in `SAFETY: [refs, steps]`.

Note that Miri, the randomized tests and `gc-verify` look for counterexamples and don't replace this document. New invariants should also be added to this document where found.

## The claim

Safe code can't cause undefined behavior through the public API. That holds for any order of steps, collections and allocations, allocation failures, caught panics, forgotten handles, and several arenas at once. It assumes that:

- the gc crate's own `unsafe impl`s of `Trace`, `Plain` and `Inline` keep their contracts
  (see [trace](#trace));
- the [assumptions](#assumptions) at the end hold.

Other crates can't add such impls. They forbid unsafe code through the workspace lints, which
`only_the_gc_crate_allows_unsafe_code` checks, so they get the traits only from the derive,
which belongs to the gc's trusted code.

Damaged memory, from a bug in this crate or from unsafe code elsewhere, is outside the claim.
[Defense in depth](#defense-in-depth) covers what the crate does about it anyway, and
[damaged memory](#damaged-memory) how far that goes.

## Invariants

### brand

Every handle to arena data (`Gc`, `Member`, `AnyRef`, `Value`, `HostRef`, `TypeTag`, `Weak`,
...) carries a lifetime `'gc` naming one step of one arena, and is only used with that step's
`Mutation`.

- `Arena::mutate`, `mutate_root` and `step` take closures generic over `'gc`, so nothing
  branded can be returned or kept past the call, and the closure can't assume `'gc` is any
  particular lifetime, `'static` included.
- `Invariant<'gc>` makes the brand invariant, so two arenas' brands never unify.
- Handles that outlive steps carry an arena id instead of a brand, checked on use: `Root`
  (`Mutation::fetch` returns `ForeignRoot`) and `Stack` (asserts). Ids come from a global
  counter and are never reused: once it runs out, `Arena::new` fails with `OutOfMemory`.
- `Gc::from_raw`, which every `Gc` comes from, requires `T: Plain<'gc>`, and `Plain` requires
  every handle in `T` to carry `'gc`. So a type branded `'static` can't be read in a step, even
  though `TypeId` ignores lifetimes.
- `Trace` types use `'gc` only as a brand, never for borrows, since roots outlive the step that
  made them.
- `Arena`, `Mutation`, `Gc`, `Root`, `Stack` and `Frame` aren't `Send` or `Sync`. `Member`,
  `Value`, `AnyRef` and `HostRef` are `Send`, but do nothing without their arena's `Mutation`,
  which can't leave its thread.

Relied on by the brand casts in `Arena::new`, `mutate`, `mutate_root`, `Mutation::root` and
`fetch`: only the lifetime changes, which changes neither layout nor validity.

### steps

A collection never runs during a step, nor a step during a collection.

- Collections need `&mut Arena`: `collect`, `collect_minor`, `collect_slice`, and `step` after
  its closure returns. Steps only borrow the heap shared, through `Mutation`.
- Inside the heap, collection entry points take `&mut Heap` and hand down a `Collecting` token,
  which only they can make.
- Nothing in a step frees, moves or rewrites the header of an existing object. Allocation only
  takes free memory, and sweeping only runs in collection slices.

Relied on by `Gc::as_ref`, `Deref` and `items`, whose `&'gc` borrows last the step;
`HostRef::get`, since host values are only freed by sweeping; and `items_mut` and the vtables'
`trace`, which take `&mut` because no step holds a reference.

### refs

In an arena that isn't corrupted, outside a collection, every object reference safe code can
reach names the header of an object that hasn't been freed, and a `Member<T>` names a `T`. That
covers `Member`s, object words in `AnyRef` and `Value`, ephemeron keys, and root and stack
slots.

- References are only made from objects: `Member::new` from a `Gc<T>`, which `alloc` or a
  `get` made, and `AnyRef` and `Value` from those. Downcasts compare the header's type with the
  vtable's `TypeId` before making a `Gc<T>`. The `from_bits` functions, which make references
  from raw bits, are test-only.
- Every crate-private function that makes or rewrites a reference from raw parts is an
  `unsafe fn` (`AnyRef::member`, `AnyRef::from_word`, `Value::from_word`, `Value::reference`,
  `Member::from_offset`, `Member::offset_mut`), so each call site states its proof. Words
  without a reference go through `Value::immediate`, which debug builds check.
- Objects are freed only by sweeping, and only when unmarked, after [reach](#reach) has marked
  everything reachable.
- Objects move only in compaction, which rewrites every reference ([moves](#moves)).

Relied on by `Member::get`, the downcasts, `Gc::as_ref`, and [headers](#headers).

### headers

Outside a collection, the header of every object a reference names ([refs](#refs)) is the one
allocation wrote, so `ty` is its type and `len` its item count.

- `Heap::build` writes the header, and `Building::finish` sets `len` to the items kept, before
  the object is colored and anything can name it. Steps don't write headers ([steps](#steps)).
- Collections write headers only to forward a moved object (`move_object`) or to wipe one that
  nothing names any more (`clear_header`, for old copies after fixup and dead objects in
  `sweep_page`).
- Forwarded headers exist only during the atomic phase. If it unwinds, the arena is corrupted
  and refuses steps ([unwind](#unwind)).

Relied on by `Object::len` and `items`, and so `Gc::items`, and by the collector's views
(`trace_with`, `items_mut`): the items are exactly the object's, and the `max_items` cap is only
a backstop. `Batch`, and with `gc-hardened` the collector, don't rely on it, since
[extents](#extents) bounds their views.

### memory

The region is `RESERVE` (twice `REGION`) bytes, initialized, mapped and readable for the arena's
whole life. Every pointer into it comes from `Heap::base`, so it has the region's provenance.

- `Backing::new` maps it anonymously, or with `alloc_zeroed` without the `mmap` feature.
  `decommit` only advises `MADV_DONTNEED`, which leaves the range mapped and readable.
- Offsets are masked with `OFFSET_MASK`, so they're aligned and below `REGION`. `layout::fits`
  and `fits_inline`, checked at compile time, keep any `T` and the items `max_items` allows
  within `REGION` of such an offset, and so inside the reservation.

Relied on by `header_at`, which reads at any masked offset, `Member::get`, `Gc::from_raw`, and
compaction's copy.

### plain

Every type in arena memory has no padding, accepts every bit pattern, and doesn't need drop.

- The derive checks that each field is `Plain` and that the type has no padding (`CHECK`). The
  gc's own impls are for integers, floats, arrays, `PhantomData`, `Lock`, `Option<Member>`,
  `AnyRef`, `Value` and `HostRef`.
- Allocation asserts `!needs_drop`.

Relied on by header reads (`Header` is plain integers), compaction copying objects byte for
byte, and [defense in depth](#defense-in-depth).

### alias

During a step, arena memory is read through shared references (`&T` from a `Gc`, `&[Item]` from
`items`) and written only through cells inside them, or where no reference reaches. During a
collection, the collector holds at most one `&mut` per object, over its value and items but not
its header, and no step's references exist.

- A `Gc<T>` covers exactly its object's value, and `items` exactly its items ([refs](#refs),
  [headers](#headers)), so references to different objects don't overlap.
- After allocation, arena types are only written through `Lock`, a cell. Headers aren't written
  during a step.
- `Building` writes new objects into memory `reserve` just took from free lines or pages, which
  no reference reaches. `alloc_inline_with`'s `init` gets `&mut` to the new items before any
  `Gc` to them exists.
- In a collection, `trace_with` and `items_mut` take `&mut` to one object at a time, within its
  own bytes ([headers](#headers), and with `gc-hardened` also [extents](#extents)). The tracer reads other headers by value through raw
  pointers, so tracing an object that refers to itself doesn't alias the `&mut`.

Relied on by `Gc::as_ref`, `items`, `Building`, the vtables' `trace`, and `items_mut`.

### extents

Every span a `Batch` writes without the barrier, and with the `gc-hardened` feature every view
the collector takes of an object, stays within that object's own bytes, whatever its header
claims. The feature costs about 10% on collections, so it's off by default.

- Start bits are page metadata, outside the region. `reserve` sets an object's, and `release`,
  sweeping and evacuation clear it when the object goes, so they mark exactly the allocated
  objects.
- `checked_view` checks the size the header claims, which bounds the value and the items,
  against the next start bit after the object, or against its page run for a large object.
  `object_span` always uses it, and `view_at` does with `gc-hardened`. When the size doesn't
  fit, `trace_object` marks the arena corrupted instead of tracing, `items_mut` returns `None`,
  and `object_span` returns `None`, so a `Batch` takes the barrier for every store.
- The collector's views only come from `view_at`: `trace_with`, `items_mut` and `gc-verify`'s
  trace. Plain `size_of`, bounded only by the page run, is for what takes no view: counting
  the lines marking keeps, and compaction's copy, which only reads the old bytes through raw
  pointers into memory just reserved for it.

`a_damaged_header_cant_stretch_a_batch` and, with the feature,
`a_damaged_length_cant_stretch_a_trace` damage a length so it covers a neighbor.

Relied on by [alias](#alias), the vtables' `trace`, `items_mut`, and `Batch`.

### reach

When a sweep frees an object, it's unmarked, and no reference safe code can reach names it.

Major cycles:

- Marking clears the marks and traces the roots: the arena root, `Root` entries, and live
  stacks (`trace_roots`).
- Storing into a marked object shades the stored value (`write_barrier`). `Lock::fill` and
  `barrier_range` shade ranges, and a `Batch` grays its object again when it ends
  (`retrace_part`). Writes to the root and to stack frames skip barriers; the atomic phase
  traces all roots again to cover them.
- Objects allocated while marking are marked, and grayed if they hold references
  (`color_marked`), so what their first values name gets marked.
- When the gray stack is full, pages are flagged `OVERFLOW` and traced whole.
- An ephemeron's value is traced once its key is marked (`settle_ephemerons`). Keys still
  unmarked at the end are cleared with their values (`clear_dead_ephemerons`) before anything is
  freed. Ephemerons outside the arena hold their keys strongly.
- Host values are marked through `HostRef`s and swept with the objects. `HostRef::get` checks
  the id anyway, so it doesn't rely on this.

Minor collections:

- Objects marked in earlier cycles stay marked, which makes them old.
- Every reference stored into an old object since the last collection is on a dirty card:
  `write_barrier` dirties the card on every store into the region, a `Batch` dirties what it
  wrote, and retiring stack frames dirties theirs.
- `minor` traces the roots and the dirty cards, so every young object reachable from an old one
  gets marked.

Sweeping:

- `sweep_page` frees only unmarked objects.
- Nothing reaches an unmarked object after the atomic phase: references to it were only in
  unmarked objects or in ephemerons, which were cleared.
- While sweeping, allocation only takes pages already swept (`SWEPT`, in `Space::reusable`),
  so a sweep never frees an object made after it started.

Relied on by [refs](#refs).

### stacks

Frame writes skip the barrier only at or above `base` of a stack's current segment. Every
collection traces `base..top` of each stack that isn't parked as a root, and voids the slots
above `top`, so each slot written without a barrier is traced or wiped before anything is freed
or moved.

- Only `Stack::live` makes the slots that skip the barrier. It checks `at >= base` and unparks
  the stack.
- `trace_roots` traces every stack record. `StackRecord::trace` voids the slots above `top` in
  `Mark` mode, which each collection's final marking uses.
- Frames stop skipping the barrier only after a barrier over all of them: in `capture`, for the
  frames below the new `base`, in `switch` and `park` (`retire`), and in `attach`, for a dropped
  stack that used the same segment.
- A dropped `Stack`'s record is let go only after a `Mark` trace.
- One live stack uses a segment at a time (`attach` panics otherwise), so no record voids
  another's frames.

Relied on by `Live::set`'s `set_unbarriered`, [reach](#reach) and [moves](#moves).

### moves

Objects move only in the atomic phase of a major cycle, and every reference that can still be
reached is rewritten to the new copy before the next step.

1. Marking dirties the card of every slot pointing into a page being compacted (`note_slot`),
   and every store while marking dirties its card anyway.
2. Allocation skips pages being compacted (`Space::reusable`), so no object made while
   marking is on one.
3. Each marked object on those pages is copied (`move_object`), and its old header holds the
   new offset.
4. Fixup traces the roots (the arena root, `Root` entries, live stacks), the dirty cards of
   marked objects that didn't move, and the new copies, and rewrites every reference to a
   forwarded header (`Tracer::edge`, `ephemeron_key`).
5. The old headers are wiped, and their space freed.

References fixup doesn't visit are in unmarked objects, which are freed unread, or above stack
tops, which were voided ([stacks](#stacks)). A panic in step 4 leaves references half
rewritten, and the arena is corrupted ([unwind](#unwind)).

Relied on by [refs](#refs).

### unwind

Every panic either leaves the invariants intact or marks the arena corrupted. A corrupted arena
refuses `mutate`, `mutate_root` and `step` (`Corrupted`), and collections do nothing. None of
this relies on a destructor safe code could skip.

| Where it can panic | What's half done | Why it's safe |
|---|---|---|
| `Trace` code in a collection (`minor`, `start`, `work`) | marks, the gray stack, forwarding | `CorruptOnUnwind` closes the arena |
| `Trace` code in a barrier (`barrier_slow`, `barrier_range`) | a stored value, partly shaded | `CorruptOnUnwind`: nothing is freed again, and the step's `mutate` returns `Corrupted` |
| `fill` or `init` in `alloc_inline*` | a reserved object | `Building`'s drop releases it, and nothing names it yet |
| the closure of `Budget::quiet` | optional allocation mode | the `Restore` guard |
| a `Batch` closure | writes without a barrier | `Batch`'s drop retraces the object |
| `attach` ("segment is already in use") | nothing: it checks before changing anything | |
| a host value's drop | nothing: values are dropped after the collection finishes | |

The guards live in the gc's own frames (`Building`, `Restore`, `CorruptOnUnwind`) or reach user
code only by `&mut` (`Batch`), so safe code can't `mem::forget` them. Forgetting a `Root` or
`Stack` only keeps what it holds alive.

### trace

A `Trace` impl hands the tracer every `Member`, `AnyRef`, `Value`, `HostRef` and `Ephemeron` it
holds, and its `NEEDS_TRACE`, `holds_refs` and `INLINE` agree with that.

- Outside the gc crate, impls only come from the derive, which traces every field, bounds every
  field type by `Trace`, computes `NEEDS_TRACE` from the fields, leaves `holds_refs` at its
  default, and sets `INLINE` along with the `Inline` impl.
- The gc's own impls follow one rule: each type parameter is traced or only in a
  `PhantomData`. There are none for Rust's collections: data that holds references
  lives in the arena, where it's charged and traced incrementally.
- `library_impls_trace_every_reference` counts the references each library impl visits.
- `Gc` has no `Trace` impl, so traced types can't hold one.

Relied on by [reach](#reach) and [moves](#moves).

## Defense in depth

The argument doesn't need these. They contain bugs and damaged memory:

- **Check bits.** References carry the type and stamp of their object's header (`Check`).
  Downcasts and the tracer compare them, and a mismatch marks the arena corrupted. Builds with
  `test` or `gc-verify` also wipe dead headers, so stale references always fail.
- **Validation.** Collector code looks objects up through `object_at`, `size_of` and `view_at`,
  which check the page metadata, start bits and sizes against the object's own bytes.
- **Caps.** Offsets are masked and `Object::len` caps lengths at `max_items`, so a damaged
  reference or header still reads inside the reservation ([memory](#memory)), as some valid
  value ([plain](#plain)).
- **`gc-verify`.** After marking and after compaction, it checks that everything reachable is
  marked and that no reference was left pointing at an old copy.

### Damaged memory

The model: between any two operations, the region's bytes, headers included, may hold
anything. What lies outside it is trusted: the page table with its start, mark and line bits,
the vtables, the host table, and the root and stack tables. Under that model:

- With `gc-hardened`, collections stay sound. Their views are bounded by trusted start bits
  ([extents](#extents)), every bit pattern is a valid value ([plain](#plain)), offsets are
  masked ([memory](#memory)), and other headers are only read by value. Without it, a damaged
  length can stretch a traced object's `&mut` over its neighbors.
- Steps don't yet. A damaged length, or a damaged reference whose check bits happen to match,
  can make a `&T` or `&[Item]` from a `Gc` cover another object, whose cells the step may then
  write. That breaks [alias](#alias).

## Assumptions

- `MADV_DONTNEED` on a private anonymous mapping leaves it mapped and readable. Linux reads
  zeros back, and other systems may keep the old bytes, which are still initialized. Making
  `decommit` unmap the range or protect it with `PROT_NONE` would break [memory](#memory).
- `TypeId::of` ignores lifetimes. `layout::type_id` relies on that to erase them, and never
  touches a value of the type.
- Rust's aliasing rules aren't final. The argument assumes the Stacked and Tree Borrows view:
  shared references to cells allow writes through other shared references to the same cells,
  raw reads outside any reference's range are fine, and a `&mut` excludes other access only to
  what it covers.
- The `unsafe_code` lint doesn't fire inside code expanded from another crate's derive. Crates
  that forbid unsafe code rely on that to use the derive.

## For the VM

The VM crate takes the workspace lints, so it adds no unsafe code and no `Trace` impls.
Continuations need nothing new from the gc: `capture`, `switch`, `park` and `Stack::write` are
the primitives, covered by [stacks](#stacks). The VM should still:

- call `Stack::set_top` before each step ends. A stale `top` doesn't break soundness, but the
  next collection voids the frames above it;
- copy captured frames back with `Stack::write` instead of running them in place, since frames
  below `base` can't be written through the stack. The stack refuses those writes (`set` and
  `write` return `false`, and `frame` returns `None`), and the segment's locks take the
  barrier, so this doesn't affect soundness either. Editing frames in place would only make a
  continuation see its earlier run's changes when it's invoked again.

## Open

- Kani harnesses for the arithmetic the unsafe code relies on: `PageIndex::overlapping`,
  `page_of`, `Bits::any_in`, `view_at`, `max_items`, `inline_size`, and the `Batch` bounds
  check.
- Steps under [damaged memory](#damaged-memory): reads that borrow a token and writes by handle
  instead of through `&T`, so no step's view can overlap a write.
