# stable_gen_map

A single-threaded, generational map that lets you:

- **insert with `&self` instead of `&mut self`,**
- keep `&T` **stable across internal resizes,**
- and use **generational keys** to avoid use-after-free bugs.

It's designed for patterns like *graphs, self-referential structures, and arenas* where you want to keep `&T` references around while still inserting new elements, and you want to be able to defer the removal of elements, such as, at the end of a videogame's frame, or turn. Great for patterns that rely on shared mutability on a single thread, and removes a lot of borrow checker struggles.

> **Important:** This crate is intentionally single-threaded. The map types are not `Sync`, and are meant to be used from a single thread only.

> **Nightly (optional):** The `CastKey` subsystem (`StableCastMap`, `DefaultCastKey`, `new_castable_key_type!`) is gated behind the **`castable`** cargo feature and requires a nightly toolchain. The core map types (`StableMap`, `StableDerefMap`) work on **stable** Rust out of the box.

---

## Getting started

Add the dependency:

```bash
cargo add stable_gen_map
```

Or in `Cargo.toml`:

```toml
[dependencies]
stable_gen_map = "0.12"
```

With the default features, the crate works on **stable** Rust — no special toolchain needed.

To enable cast keys (requires **nightly**):

```toml
[dependencies]
stable_gen_map = { version = "0.12", features = ["castable"] }
```

```bash
rustup override set nightly
```

---

## Core types

- **`StableMap<K, T>`** — A stable generational map storing each `T` in a `Box`. The `Box` allocation is **reused** across remove/insert cycles, so a remove followed by an insert into the same slot incurs no heap traffic. This is generally what you want.

- **`StableDerefMap<K, Derefable>`** — A stable generational map where each element is a smart pointer that implements `DerefGenMapPromise`. You get stable references to `Deref::Target`, even if the underlying `Vec` reallocates. This is the "advanced" variant for `Box<T>`, `Rc<T>`, `Arc<T>`, `&T`, or custom smart pointers.

- **`BoxStableDerefMap<K, T>`** — Type alias for `StableDerefMap<K, Box<T>>`. Preferred over `StableMap` if your element needs to be boxed anyway.

- **`StableCastMap<CK, D>`** *(requires the `castable` feature, nightly only)* — A wrapper around `StableDerefMap` that uses `CastKey` for type-erased heterogeneous storage. Supports implicit key upcasting via `CoerceUnsized`, so a `DefaultCastKey<MyStruct>` can be implicitly coerced to `DefaultCastKey<dyn Trait>`. Useful for storing `Box<dyn Any>` and retrieving concrete types.

Keys implement the `Key` trait; you can use the provided `DefaultKey` or define your own with the `new_key_type!` macro (e.g. with smaller index/generation types or map-id checking).

---

## API overview

### Insertion (all take `&self`)

- `insert(&self, value) -> (K, &T)`
- `insert_with_key(&self, f: impl FnOnce(K) -> T) -> (K, &T)`
- `try_insert_with_key(&self, f: impl FnOnce(K) -> Result<T, E>) -> Result<(K, &T), E>`

### Lookup

- `get(&self, key) -> Option<&T>`
- `get_mut(&mut self, key) -> Option<&mut T>`
- `get_by_index_only(&self, idx) -> Option<(K, &T)>` — ignores generation
- `get_by_index_only_mut(&mut self, idx) -> Option<(K, &mut T)>`
- `map[key]` / `map[key]` — `Index` and `IndexMut` impls (panics on miss)

### Removal and mutation (`&mut self`)

- `remove(&mut self, key) -> Option<T>`
- `clear(&mut self)`
- `retain(&mut self, f: FnMut(K, &mut T) -> bool)`
- `drain(&mut self) -> Drain` — removes all elements, yielding `(K, T)`

### Iteration

- `snapshot(&self) -> Vec<(K, &T)>` — safe, heap-allocates one `Vec`
- `snapshot_refs(&self) -> Vec<&T>`
- `snapshot_keys(&self) -> Vec<K>`
- `iter_mut(&mut self)` — yields `(K, &mut T)`
- `into_iter(self)` — consumes the map, yields `(K, T)`
- `iter_unsafe(&self)` — unsafe, zero-allocation; caller must not insert while iterating

### Capacity

- `new() -> Self`
- `with_capacity(n) -> Self`
- `reserve(&self, additional)`
- `try_reserve(&mut self, additional) -> Result<(), TryReserveError>`
- `capacity(&self) -> usize`
- `len(&self) -> usize`

### Cloning

- `Clone::clone` — safe two-phase snapshot clone (tolerates `T::clone` re-entering the map)
- `clone_efficiently_mut(&mut self)` — faster single-pass clone; safe because `&mut self` prevents the stored type's `Clone` from mutating the map

---

## Complexity

- `get` / `get_mut` / `remove` are **O(1)**.
- `insert` is **O(1) amortized** (O(1) unless a resize happens).

---

## Lifetime / safety model

- You can hold `&T` from the map and still call `insert` (which only needs `&self`).
- `remove` and `clear` need `&mut self`, so you can't free elements while there are outstanding borrows — enforced by the borrow checker.
- Generational keys mean stale keys simply return `None` instead of aliasing newly inserted elements.
- When a slot's generation counter overflows, that slot is permanently retired (never reused), avoiding any possibility of aliasing.

---

## Custom keys

Use the `new_key_type!` macro to create custom key types, similar to slotmap's `new_key_type!`:

```rust
use stable_gen_map::new_key_type;

// Basic key (same as DefaultKey):
new_key_type! {
    pub struct PlayerKey;
}

// Custom index/generation sizes (smaller memory footprint):
new_key_type! {
    pub struct SmallKey(u16, u16);
}

// Key with map-id checking (keys are bound to the map that created them):
new_key_type! {
    pub struct IdentifiedKey identified;
}

// Custom sizes + map-id:
new_key_type! {
    pub struct SmallIdentifiedKey(u16, u16) identified;
}
```

The `identified` variant stamps a unique `MapId` into every key and slot, so using a key from one map on another returns `None` instead of silently accessing wrong data. This is useful for catching bugs in complex systems with multiple maps.

---

## Comparison to other data structures

`StableMap` lives in the same space as generational arenas / slot maps, but it's aimed at a slightly different pattern: **inserting with `&self` while keeping existing `&T` references alive**, in a single-threaded setting where you still sometimes remove elements at well-defined points (e.g. end of a videogame frame).

| Crate | Insert API | Removals | Main focus |
|---|---|---|---|
| `stable_gen_map::StableMap` | `fn insert(&self, T) -> (K, &T)` | Yes (`&mut self`) | Stable `&T` across growth, single-threaded |
| `slotmap::SlotMap` | `fn insert(&mut self, V) -> K` | Yes (`&mut self`) | General-purpose generational map |
| `generational_arena::Arena` | `fn insert(&mut self, T) -> Index` | Yes (`&mut self`) | Simple arena with deletion |
| `slab::Slab` | `fn insert(&mut self, T) -> usize` | Yes (`&mut self`) | Reusable indices, pre-allocated storage |
| `sharded_slab::Slab` | `fn insert(&self, T) -> Option<usize>` | Yes (`&self`) | Concurrent slab for multi-threaded use |

### When to use `stable_gen_map`

Use `stable_gen_map` when:

- You want to **insert using only a shared reference** (`&self`), not `&mut self`.
- You want to use patterns that do not rely heavily on ECS.
- You need to **hold on to `&T` from the map while also inserting new elements** into the same map.
- You like **generational keys**.
- You're in a **single-threaded** or **scoped-thread** world.
- You still want to **remove elements at specific points** in your logic, such as:
  - at the end of a videogame frame,
  - at the end of a simulation tick,
  - during a periodic "cleanup" or GC-like pass.

If you don't specifically need those properties, you could take a look at `slotmap`, `slab`, `sharded-slab`, or `generational-arena`.

---

## Basic example (using `StableMap`)

This shows the main selling point: **insert with `&self`** and indirect references via keys.

```rust
use std::cell::{Cell, RefCell};

use stable_gen_map::key::DefaultKey;
use stable_gen_map::stable_map::StableMap;

#[derive(Debug)]
struct Entity {
    key: DefaultKey,
    name: String,
    parent: Cell<Option<DefaultKey>>,
    children: RefCell<Vec<DefaultKey>>,
}

impl Entity {
    /// Add a child *from this entity* using only `&self` and `&StableMap`.
    /// Returns both the child's key and a stable `&Entity` reference.
    fn add_child<'m>(
        &self,
        map: &'m StableMap<DefaultKey, Entity>,
        child_name: &str,
    ) -> (DefaultKey, &'m Entity) {
        let parent_key = self.key;

        // No &mut reference to map required for the insert
        let (child_key, child_ref) = map.insert_with_key(|k| Entity {
            key: k,
            name: child_name.to_string(),
            parent: Cell::new(Some(parent_key)),
            children: RefCell::new(Vec::new()),
        });

        // Record the relationship using interior mutability inside the value.
        // No need to re-get the parent, since the insert did not need &mut.
        self.children.borrow_mut().push(child_key);

        (child_key, child_ref)
    }
}

fn main() {
    let mut map: StableMap<DefaultKey, Entity> = StableMap::new();

    // Create the root entity. We get an `&Entity`, not `&mut Entity`.
    let (root_key, root) = map.insert_with_key(|k| Entity {
        key: k,
        name: "root".into(),
        parent: Cell::new(None),
        children: RefCell::new(Vec::new()),
    });

    // Root spawns a child using only `&self` + `&StableMap`.
    // An ECS pattern would require a system to do these operations,
    // but with StableMap the instance itself can do the spawning.
    let (child_key, child) = root.add_child(&map, "child");

    // That child spawns a grandchild, again only `&self` + `&StableMap`.
    let (grandchild_key, grandchild) = child.add_child(&map, "grandchild");

    // Everything stays wired up via generational keys.
    // We do not need to re-get the `root` and `child` references,
    // since the inserts did not require a &mut reference.
    assert_eq!(root.children.borrow().as_slice(), &[child_key]);
    assert_eq!(child.parent.get(), Some(root_key));
    assert_eq!(child.children.borrow().as_slice(), &[grandchild_key]);
    assert_eq!(grandchild.parent.get(), Some(child_key));

    // And the references we got from `add_child` are the same as `get(...)`.
    assert!(std::ptr::eq(child, map.get(child_key).unwrap()));
    assert!(std::ptr::eq(grandchild, map.get(grandchild_key).unwrap()));
}
```

---

## Cast keys (heterogeneous maps, `castable` feature)

`StableCastMap` lets you store different concrete types in the same map behind `Box<dyn Any>`, and look them up with typed keys. Key upcasting is implicit via `CoerceUnsized`:

```rust
#![feature(ptr_metadata, coerce_unsized, unsize)]

use std::any::Any;
use stable_gen_map::cast_key::DefaultCastKey;
use stable_gen_map::stable_cast_map::StableBoxCastMap;

struct Cat { name: String }
struct Dog { name: String }

fn main() {
  let mut map: StableBoxCastMap<DefaultCastKey<dyn Any>, dyn Any> =
          StableBoxCastMap::new();

  // Insert returns the map's key type: DefaultCastKey<dyn Any>
  let (dyn_key, _) = map.insert(Box::new(Cat { name: "Whiskers".into() }));

  // Downcast the dyn key to a concrete typed key
  if let Some(cat_key) = map.downcast_key::<DefaultCastKey<Cat>>(dyn_key) {
    // Look up with the concrete key — returns &Cat
    let cat: &Cat = map.get(cat_key).unwrap();
    assert_eq!(cat.name, "Whiskers");
  }
}
```

### Inner keys

Every `CastKey` carries pointer metadata (e.g. a vtable pointer for `dyn Trait`) alongside the generational index and map id. The `CastKey` trait exposes an associated type `InnerKey` — this is the same key but *without* the pointer metadata, i.e. the type of key the backing `GenMap` actually uses. By default this is `DefaultMapKey<Idx, Gen>`.

You can extract the inner key from any cast key with `inner_key()`, and use it to access the map directly without needing pointer metadata:

```rust
// Insert returns a DefaultCastKey<dyn Any> (fat key with vtable metadata)
let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

// Strip the metadata to get a DefaultMapKey<u32, u32> (thin key)
let inner = cast_key.inner_key();

// Look up using the inner key — returns &dyn Any (the map's stored target)
let val = map.get_by_inner_key(inner).unwrap();
assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
```

The inner key methods on `StableCastMap`:

- `get_by_inner_key(&self, key) -> Option<&D::Target>` — shared lookup, returns the deref target directly
- `get_mut_by_inner_key(&mut self, key) -> Option<&mut D::Target>` — mutable lookup
- `remove_by_inner_key(&mut self, key) -> Option<D>` — removal, returns the owned smart pointer

These skip the metadata reconstruction step, so they're slightly cheaper than `get`/`get_mut`/`remove`. They're also useful when you only have the inner key (e.g. stored in a data structure that doesn't need to know about the concrete type behind the pointer).

The `InnerKey` associated type is user-configurable via the `CastKey` trait, so custom cast key types can choose their own inner key type as long as it implements `Key` with matching `Idx` and `Gen` types.

---

## License

MIT