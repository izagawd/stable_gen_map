# stable_gen_map

A single-threaded, generational map that lets you **insert with `&self` instead
of `&mut self`** — keeping `&T` references alive (stable across internal `Vec`
resizes) while you insert — and uses **generational keys**, so stale keys return
`None` instead of aliasing a new value.

It's aimed at patterns like *graphs, self-referential structures, and arenas*
where you want to hold `&T` around while inserting, and defer removals to
well-defined points (e.g. the end of a videogame frame or simulation tick). It
leans on shared mutability on a single thread and removes a lot of borrow-checker
friction.

> **Important:** This crate is intentionally single-threaded. The map types are
> not `Sync` and are meant to be used from a single thread only.

---

## Basic example

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

## API and safety model

Inserts take `&self`:

- `insert(&self, value: T) -> K`
- `insert_with_key(&self, f: impl FnOnce(K) -> T) -> K`
- `try_insert_with_key(&self, f: impl FnOnce(K) -> Result<T, E>) -> Result<K, E>`

Reads, mutation, and removal work as usual: `get(&self) -> Option<&T>`,
`get_mut(&mut self) -> Option<&mut T>`, `remove(&mut self) -> Option<T>`, plus
`len`, `is_empty`, and `clear`.

`get` / `get_mut` / `remove` are O(1); `insert` is O(1) amortized (O(1) unless a
resize happens).

The safety model follows from those signatures:

- You can hold `&T` from the map and still call `insert`, because `insert` only
  needs `&self`.
- `remove` and `clear` need `&mut self`, so the borrow checker prevents you from
  freeing elements while `&T` references are still alive.
- Generational keys mean a stale key returns `None` rather than aliasing a newly
  inserted element. When a slot's generation overflows it is permanently retired
  and never reused, so a stale key can never match a different value.

---

## Core types

### General-purpose maps

- `StableGenMap<K, T>`
  Stores a sized `T` in a `Box`. Slot reuse needs no new allocation. This is
  usually what you want.

- `StableDerefMap<K, Ptr>`
  Each element is a **smart pointer** implementing `DerefGenMapPromise`; you get
  stable references to `Deref::Target` even if the backing `Vec` reallocates.
  The "advanced" variant for `Box<T>`, `Rc<T>`, `Arc<T>`, `&T`, or custom smart
  pointers.

- `BoxStableDerefMap<K, T>`
  Alias for `StableDerefMap<K, Box<T>>`: the map owns `T` via `Box<T>`, you still
  insert with `&self`, and you get stable `&T` / `&mut T`. Prefer it over
  `StableGenMap` when your element needs to be boxed anyway.

### Type-erased maps *(requires the `castable` feature, nightly only)*

- `StableCastMap<C>` — the safe, recommended API for **type-erased heterogeneous
  storage** (e.g. `Box<dyn Any>`) with castable keys. Each map gets a unique
  `MapId` on creation, and every `StableCastKey` carries it, so a key from map A
  used on map B returns `None` instead of causing UB. `C` is the per-slot storage
  strategy (a `SlotStorage` implementor such as `DerefSlot<K, Box<dyn Any>>`); use
  the alias `StableBoxCastMap<K, T>` for the common `Box` case.

- `UnsafeCastMap<C>` — the low-level building block for `StableCastMap`. Same
  typed lookups via `CastKey`, but `get`, `get_mut`, and `downcast_key` are
  `unsafe` because no map-id check is performed. Use it when building your own
  safe abstraction; `UnsafeBoxCastMap<K, T>` covers the common case.

Keys implement the `Key` trait; use the provided `DefaultKey` or define your own
(e.g. with smaller index / generation types).


---

## The `castable` feature (nightly only)

Enables `StableCastMap` and `UnsafeCastMap`, which use keys that can be cast.
These rely on the nightly features `ptr_metadata`, `coerce_unsized`, and `unsize`.

```toml
[dependencies]
stable_gen_map = { version = "0.24", features = ["castable"] }
```

The two layers — the safe `StableCastMap` and the low-level `unsafe`
`UnsafeCastMap` — are described above. For the common case of `Box<dyn Any>`
with `DefaultKey`, use the aliases `StableBoxCastMap<DefaultKey, dyn Any>` and
`UnsafeBoxCastMap<DefaultKey, dyn Any>`.

A **cast key** is a typed handle into the erased map: it carries the value's
type both as a type parameter and as stored pointer metadata, so `map.get(key)`
returns a correctly typed `&T` (e.g. `&Dog`) with no `downcast_ref` at the call
site.

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
    let dog_key: StableCastKey<Dog> = map.insert_sized(Box::new(Dog { name: "Rex".into() }));

    // Upcast the key when you need the erased form.
    let dyn_key: StableCastKey<dyn Any> = dog_key.upcast::<dyn Any>();

    // Downcast back to the concrete type.
    let recovered: StableCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    assert_eq!(map.get(recovered).unwrap().name, "Rex");
}

struct Dog { name: String }
```

Since the keys of the cast maps store pointer metadata directly (not inside a `NonNull`),
implicit `CoerceUnsized` is not available, hence the `.upcast()` method.

### Clone semantics

When a `StableCastMap` is cloned, the clone receives a **fresh map identity**.
Keys from the original are not valid on the clone; use iteration (`snapshot`,
`iter_mut`, `drain`) to obtain new keys for the cloned data.

---

## Internals

The invariants the map's internals rely on (generation parity, overflow
retirement, free-list consistency, `num_elements` accuracy, NonZero key
generation) live in [INTERNALS.md](INTERNALS.md). You only need them if you're
implementing a custom `SlotStorage`, using `from_raw_parts`, or building on top of
`GenMap` using `unsafe`.
