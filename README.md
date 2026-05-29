# stable_gen_map

A single-threaded, generational map that lets you:

- **insert with `&self` instead of `&mut self`,**
- keep `&T` **stable across internal resizes,**
- and use **generational keys** to avoid use-after-free bugs.

It's designed for patterns like *graphs, self-referential structures, and arenas* where you want to keep `&T` references around while still inserting new elements, and you want to be able to defer the removal of elements, such as, at the end of a videogame's frame, or turn.
Great for patterns that rely on shared mutability on a single thread, and removes a lot of borrow checker struggles.

> **Important:** This crate is intentionally single-threaded. The map types are not `Sync`, and are meant to be used from a single thread only.

---

## Basic example

This shows the main selling point: **insert with `&self`** and indirect references via keys.

```rust
use stable_gen_map::key::DefaultKey;
use stable_gen_map::stable_gen_map::StableGenMap;

fn main() {
  let map = StableGenMap::<DefaultKey, String>::new();

  // insert() only needs &self
  let key_a = map.insert("hello".into());
  let key_b = map.insert("world".into());

  // get() also only needs &self, so references coexist with further inserts
  let ref_a = map.get(key_a).unwrap();
  let ref_b = map.get(key_b).unwrap();
  println!("{ref_a} {ref_b}");

  // References survive further inserts, even if the backing Vec reallocates
  for i in 0..1000 {
    map.insert(format!("item {i}"));
  }
  println!("still valid: {ref_a} {ref_b}");

  // Removal needs &mut self — the borrow checker enforces
  // that no &T references are alive when you remove
  let mut map = map;
  assert_eq!(map.remove(key_a), Some("hello".into()));
  assert!(map.get(key_a).is_none()); // stale key returns None
}
```

---

## What you get

- `insert(&self, value: T) -> K`
- `insert_with_key(&self, f: impl FnOnce(K) -> T) -> K`
- `try_insert_with_key(&self, f: impl FnOnce(K) -> Result<T, E>) -> Result<K, E>`

All of these only need `&self`, not `&mut self`.

- `get(&self, key: K) -> Option<&T>`
- `get_mut(&mut self, key: K) -> Option<&mut T>`
- `remove(&mut self, key: K) -> Option<T>`
- `len(&self) -> usize`
- `is_empty(&self) -> bool`
- `clear(&mut self)`

**Complexity**

- `get` / `get_mut` / `remove` are O(1).
- `insert` is O(1) amortized (O(1) unless a resize happens).

**Lifetime / safety model**

- You can hold `&T` from the map and still call `insert` (which only needs `&self`).
- `remove` and `clear` need `&mut self`, so you can't free elements while there are outstanding borrows – enforced by the borrow-checker.
- Generational keys (`Key::Gen`) mean stale keys simply return `None` instead of aliasing newly inserted elements.
- When a slot's generation overflows, it is permanently retired and never reused — no stale key can ever match a different value.

---

## Core types

### General-purpose maps

- `StableGenMap<K, T>`  
  A stable generational map storing a sized `T` in a `Box`. Reusing slots does not need any new allocation. This is generally what you would want.

- `StableDerefMap<K, Ptr>`  
  A stable generational map where each element is a **smart pointer** that
  implements 
  `DerefGenMapPromise`. You get stable references to `Deref::Target`,
  even if the underlying `Vec` reallocates.  
  This is the "advanced" variant for `Box<T>`, `Rc<T>`, `Arc<T>`, `&T`, or
  custom smart pointers.

- `BoxStableDerefMap<K, T>`  
  Type alias for `StableDerefMap<K, Box<T>>`.  
  This is the most ergonomic "owning" deref-based map: the map owns `T` via
  `Box<T>`, you still insert with `&self`, and you get stable `&T`/`&mut T`
  references. Preferred over `StableGenMap` if your element needs to be boxed anyways.

### Type-erased maps *(requires the `castable` feature, nightly only)*

- **`StableCastMap<C>`**  
  A safe wrapper around `UnsafeCastMap` that supports **type-erased heterogeneous storage** (e.g. `Box<dyn Any>`) with castable keys. Each map has a unique `MapId` assigned on creation, and every `StableCastKey` carries the map's id so that cross-map misuse returns `None` instead of causing UB. The type parameter `C` is the per-slot storage strategy (a `SlotStorage` implementor such as `DerefSlot<K, Box<dyn Any>>`). Use the convenience alias `StableBoxCastMap<K, T>` for the common `Box`-based case. See the [Castable maps](#the-castable-feature-nightly-only) section below.

- **`UnsafeCastMap<C>`**  
  The low-level building block for `StableCastMap`. Provides the same typed lookups via `CastKey`, but `get`, `get_mut`, and `downcast_key` are `unsafe` because no map-id check is performed. Useful when you are building your own safe abstraction on top. Use `UnsafeBoxCastMap<K, T>` for the common case.

Keys implement the `Key` trait; you can use the provided `DefaultKey` or define your own (e.g. with smaller index / generation types).

---

## Comparison to other data structures

`StableGenMap` lives in the same space as generational arenas / slot maps, but it's aimed at a slightly different pattern: **inserting with `&self` while keeping existing `&T` references alive**, in a single-threaded setting where you still sometimes remove elements at well-defined points (e.g. end of a videogame frame).


Rough comparison:

| Crate                             | Insert API                              |             Removals                           |    Main focus            |
|----------------------------------|------------------------------------------|----------------------------|-------------------------------|
| `stable_gen_map::StableGenMap`   | `fn insert(&self, T) -> K`               | Yes (But with &mut this time) | Stable `&T` across growth, single-threaded      |
| `slotmap::SlotMap`               | `fn insert(&mut self, V) -> K`           | Yes (with &mut)            | General-purpose generational map                |
| `generational_arena::Arena`      | `fn insert(&mut self, T) -> Index`       | Yes (with &mut)            | Simple arena with deletion                      |
| `slab::Slab`                     | `fn insert(&mut self, T) -> usize`       | Yes (with &mut)            | Reusable indices, pre-allocated storage         |
| `sharded_slab::Slab`             | `fn insert(&self, T) -> Option<usize>`   | Yes (with &)      | Concurrent slab for multi-threaded use |

### When to use `stable_gen_map`

Use `stable_gen_map`  when:

- You want to **insert using only a shared reference** (`&self`), not `&mut self`.
- You want to use patterns that do not rely heavily on ECS
- You need to **hold on to `&T` from the map while also inserting new elements** into the same map.
- You like **generational keys**.
- You're in a **single-threaded** or **scoped-thread** world.
- You still want to **remove elements at specific points** in your logic, such as:
  - at the end of a videogame frame,
  - at the end of a simulation tick,
  - during a periodic "cleanup" or GC-like pass.

If you don't specifically need those properties, you could take a look at `slotmap`, `slab`, `sharded-slab`, or `generational-arena`

---

## The `castable` feature (nightly only)

The `castable` feature enables `CastKey`, `StableCastKey`, `StableCastMap`, and `UnsafeCastMap`. These rely on the nightly features `ptr_metadata`, `coerce_unsized`, and `unsize`.

```toml
[dependencies]
stable_gen_map = { version = "0.17", features = ["castable"] }
```

### What it provides

There are two layers:

1. **`StableCastMap<C>`** — the safe, recommended API. Each map gets a unique `MapId` on creation. Keys are `StableCastKey<T, K>`, which carry the map id alongside generational index and pointer metadata. Every keyed lookup checks the map id first, so a key from map A used on map B simply returns `None`.

2. **`UnsafeCastMap<C>`** — the low-level layer. Keys are `CastKey<T, K>` (no map id). The `get`, `get_mut`, and `downcast_key` methods are `unsafe` because the caller must guarantee the key's ptr metadata matches the concrete type of the value stored at the slot it resolves to. Use this when you're building your own safe wrapper.
a
Both maps are parameterized over a single `SlotStorage` implementor `C` that determines the backing key type, the stored smart pointer, and the output type. For the common case of `Box<dyn Any>` with `DefaultKey`, use the convenience aliases `StableBoxCastMap<DefaultKey, dyn Any>` and `UnsafeBoxCastMap<DefaultKey, dyn Any>`.

### Quick example

```rust
use stable_gen_map::cast_key::StableCastKey;
use stable_gen_map::key::DefaultKey;
use stable_gen_map::stable_cast_map::StableBoxCastMap;
use std::any::Any;

type CastMap = StableBoxCastMap<DefaultKey, dyn Any>;

fn main() {
    let map: CastMap = CastMap::new();

    // Insert a concrete type into a dyn Any map.
    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    // dog_key: StableCastKey<Dog>

    // Upcast the key when you need the erased form.
    let dyn_key: StableCastKey<dyn Any> = dog_key.upcast::<dyn Any>();

    // Downcast back to the concrete type.
    let recovered: StableCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    assert_eq!(map.get(recovered).unwrap().name, "Rex");
}

struct Dog { name: String }
```

### Key types

| Type | Map id? | `unsafe` access? | Use case |
|---|---|---|---|
| `StableCastKey<T, K>` | Yes | No — lookups are safe | General use with `StableCastMap` |
| `CastKey<T, K>` | No | Yes — caller must ensure metadata validity | Low-level use with `UnsafeCastMap` |

`K` defaults to `DefaultKey` (which uses `u32` for both index and generation)

### Available insert methods

| Method | Key given to closure | Returned key type |
|---|---|---|
| `insert(value)` | — | `StableCastKey<C::Output>` (erased) |
| `insert_with_key(\|inner_key\| ...)` | `C::Key` (e.g. `DefaultKey`) | `StableCastKey<C::Output>` (erased) |
| `insert_sized(value)` | — | `StableCastKey<Concrete>` |
| `insert_sized_with_key(\|typed_key\| ...)` | `StableCastKey<Concrete>` | `StableCastKey<Concrete>` |
| `insert_as(value)` | — | `StableCastKey<Source::Target>` |
| `insert_as_with_key(\|inner_key\| ...)` | `C::Key` (e.g. `DefaultKey`) | `StableCastKey<Source::Target>` |

### Key upcasting

Since `StableCastKey` stores pointer metadata directly (not inside a `NonNull`), implicit `CoerceUnsized` is not available. Instead, use the `.upcast()` method:

```rust
let concrete_key: StableCastKey<Dog> = map.insert_sized(Box::new(dog));
let erased_key: StableCastKey<dyn Any> = concrete_key.upcast::<dyn Any>();
```

### Clone semantics

When a `StableCastMap` is cloned, the clone receives a **fresh map identity**. Keys from the original are not valid on the clone. Use iteration (`snapshot`, `iter_mut`, `drain`) to obtain new keys for the cloned data.

---

## General Internal invariants

These are the rules the map's internals rely on. You only need to care about these if you're implementing a custom `SlotStorage`, using `from_raw_parts`, or building on top of `GenMap` directly.

- **Generation parity.** Even generation means vacant, odd generation means occupied. A freshly created slot starts at generation 0 (even, vacant). Each insert increments the generation by 1 (even → odd, becoming occupied). Each remove increments the generation by 1 (odd → even, becoming vacant). The `FreeGuard` rollback increments by 2 (even → even, staying vacant) to maintain parity.

- **Generation overflow retirement.** When a slot's generation cannot be incremented further (checked via `checked_add`), the slot's generation is set to 0 and the slot is **not** returned to the free list. It is permanently retired and will never be reused. This ensures a stale key cannot accidentally match a different value at the same index.

- **Free-list consistency.** The free list is a singly linked list threaded through the `vacant` field of each vacant slot's `SlotData` union. `next_free` points to the head. Each vacant slot's `vacant` field points to the next free slot, or `None` at the tail. Occupied slots and retired slots (generation 0 after overflow) are not in the free list.

- **`num_elements` accuracy.** The `num_elements` cell must exactly equal the number of slots whose generation is odd (occupied). It is incremented by 1 on each successful insert and decremented by 1 on each successful remove.

- **NonZero key generation.** `KeyData.generation` is stored as `Generation::AsNonZero` (e.g. `NonZero<u32>`). This is sound because keys are only constructed when a slot transitions to occupied (odd generation), and odd unsigned integers are always non-zero. Code that constructs a `KeyData` must ensure the generation value is non-zero, or use `try_into().unwrap_unchecked()` only after verifying occupancy.