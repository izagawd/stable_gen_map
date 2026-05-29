# Internal invariants

These are rules `GenMap`'s internals rely on. You only need to care about
these if you're implementing a custom `SlotStorage`, using `from_raw_parts`, or
building on top of `GenMap` with `unsafe`. Ordinary users of `StableGenMap`,
`StableDerefMap`, or the castable maps can ignore this file.

- **Generation parity.** Even generation means vacant, odd generation means
  occupied. A freshly created slot starts at generation 0 (even, vacant). Each
  insert increments the generation by 1 (even → odd, becoming occupied). Each
  remove increments the generation by 1 (odd → even, becoming vacant). The
  `FreeGuard` rollback increments by 2 (even → even, staying vacant) to maintain
  parity.

- **Generation overflow retirement.** When a slot's generation cannot be
  incremented further (checked via `checked_add`), the slot's generation is set
  to 0 and the slot is **not** returned to the free list. It is permanently
  retired and will never be reused. This ensures a stale key cannot accidentally
  match a different value at the same index.

- **Free-list consistency.** The free list is a singly linked list threaded
  through the `vacant` field of each vacant slot's `SlotData` union. `next_free`
  points to the head. Each vacant slot's `vacant` field points to the next free
  slot, or `None` at the tail. Occupied slots and retired slots (generation 0
  after overflow) are not in the free list.

- **`num_elements` accuracy.** The `num_elements` cell must exactly equal the
  number of slots whose generation is odd (occupied). It is incremented by 1 on
  each successful insert and decremented by 1 on each successful remove.

- **NonZero key generation.** `KeyData.generation` is stored as
  `Generation::AsNonZero` (e.g. `NonZero<u32>`). This is sound because keys are
  only constructed when a slot transitions to occupied (odd generation), and odd
  unsigned integers are always non-zero. Code that constructs a `KeyData` must
  ensure the generation value is non-zero, or use `try_into().unwrap_unchecked()`
  only after verifying occupancy.
