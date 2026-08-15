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
use stable_gen_map::DefaultKey;
use stable_gen_map::StableGenMap;

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

## Internals

The invariants the map's internals rely on (generation parity, overflow
retirement, free-list consistency, `num_elements` accuracy, NonZero key
generation) live in [INTERNALS.md](INTERNALS.md). You only need them if you're
implementing a custom `SlotStorage`, or building on top of
`GenMap` using `unsafe`.
