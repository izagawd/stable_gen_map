# Internal invariants

These are rules `GenMap`'s internals rely on. You only need to care about
these if you're implementing a custom `SlotStorage`, or
building on top of `GenMap` with `unsafe`. Ordinary users of `StableGenMap` or
`StableDerefMap` can ignore this file.

- **Generation parity.** Even generation means vacant, odd generation means
  occupied. A freshly created slot starts at generation 0 (even, vacant). Each
  insert increments the generation by 1 (even → odd, becoming occupied). Each
  remove increments the generation by 1 (odd → even, becoming vacant). The
  `FreeGuard` rollback increments by 2 (even → even, staying vacant) to maintain
  parity.

- **Generation overflow: retire or wrap.** When a slot's generation cannot be
  incremented further (checked via `checked_add`), the generation is set to 0
  and behavior depends on the key type's `Key::WRAP_ON_OVERFLOW` constant. When
  it is `false` (the default), the slot is **not** returned to the free list. It
  is permanently retired and never reused, so a stale key cannot accidentally
  match a different value at the same index. When it is `true`, the slot **is**
  returned to the free list and reused; this is memory-safe (a key only carries
  an odd generation and only matches an occupied slot) but a pre-overflow key
  can then match a new value at that index

- **Free-list consistency.** The free list is a singly linked list threaded
  through the `vacant` field of each vacant slot's `SlotData` union. `next_free`
  points to the head. Each vacant slot's `vacant` field points to the next free
  slot, or `None` at the tail. Occupied slots are not in the free list, and
  neither are retired slots.

- **`num_elements` accuracy.** The `num_elements` cell must exactly equal the
  number of slots whose generation is odd (occupied). It is incremented by 1 on
  each successful insert and decremented by 1 on each successful remove.

- **NonZero key generation.** `KeyData.generation` is stored as
  `Generation::AsNonZero` (e.g. `NonZero<u32>`). This is sound because keys are
  only constructed when a slot transitions to occupied (odd generation), and odd
  unsigned integers are always non-zero. Code that constructs a `KeyData` must
  ensure the generation value is non-zero, or use `try_into().unwrap_unchecked()`
  only after verifying occupancy.
