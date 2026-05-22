# stable_gen_map

A single-threaded, generational map that lets you:

- **insert with `&self` instead of `&mut self`,**
- keep `&T` **stable across internal resizes,**
- and use **generational keys** to avoid use-after-free bugs.

It's designed for patterns like *graphs, self-referential structures, and arenas* where you want to keep `&T` references around while still inserting new elements, and you want to be able to defer the removal of elements, such as, at the end of a videogame's frame, or turn.
Great for patterns that rely on shared mutability on a single thread, and removes a lot of borrow checker struggles.

> **Important:** This crate is intentionally single-threaded. The map types are not `Sync`, and are meant to be used from a single thread only.

---

## Core types

- `StableGenMap<K, T>`  
  A stable generational map storing a sized `T` in a `Box`. Reusing slots does not need any new allocation. This is generally what you would want.

- `StableDerefMap<K, Derefable>`  
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

- **`StableCastMap<D>`** *(requires the `castable` feature, nightly only)*  
  A safe wrapper around `UnsafeCastMap` that supports **type-erased heterogeneous storage** (e.g. `Box<dyn Any>`) with castable keys. Each map has a unique `MapId` assigned on creation, and every `StableCastKey` carries the map's id so that cross-map misuse returns `None` instead of causing UB. See the [Castable maps](#the-castable-feature-nightly-only) section below.

- **`UnsafeCastMap<D>`** *(requires the `castable` feature, nightly only)*  
  The low-level building block for `StableCastMap`. Provides the same typed lookups via `CastKey`, but `get`, `get_mut`, and `downcast_key` are `unsafe` because no map-id check is performed. Useful when you are building your own safe abstraction on top (e.g. a GC).

Keys implement the `Key` trait; you can use the provided `DefaultKey` or define your own (e.g. with smaller index / generation types).

---

## What you get

- `insert(&self, value: T) -> (K, &T)`
- `insert_with_key(&self, f: impl FnOnce(K) -> T) -> (K, &T)`
- `try_insert_with_key(&self, f: impl FnOnce(K) -> Result<T, E>) -> Result<(K, &T), E>`

All of these only need `&self`, not `&mut self`.

- `get(&self, key: K) -> Option<&T>`
- `get_mut(&mut self, key: K) -> Option<&mut T>`
- `remove(&mut self, key: K) -> Option<T>`
- `len(&self) -> usize`
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

## The `castable` feature (nightly only)

The `castable` feature enables `CastKey`, `StableCastKey`, `StableCastMap`, and `UnsafeCastMap`. These rely on the nightly features `ptr_metadata`, `coerce_unsized`, and `unsize`.

```toml
[dependencies]
stable_gen_map = { version = "0.12", features = ["castable"] }
```

### What it provides

There are two layers:

1. **`StableCastMap<D>`** — the safe, recommended API. Each map gets a unique `MapId` on creation. Keys are `StableCastKey<T>`, which carry the map id alongside generational index and pointer metadata. Every keyed lookup checks the map id first, so a key from map A used on map B simply returns `None`.

2. **`UnsafeCastMap<D>`** — the low-level layer. Keys are `CastKey<T>` (no map id). The `get`, `get_mut`, and `downcast_key` methods are `unsafe` because the caller must guarantee the key's metadata is valid. Use this when you're building your own safe wrapper.

Both maps are parameterized over the smart pointer type `D` (e.g. `Box<dyn Any>`) and optional `Idx`/`Gen` types (defaulting to `u32`).

### Quick example

```rust
use stable_gen_map::cast_key::StableCastKey;
use stable_gen_map::stable_cast_map::StableCastMap;
use std::any::Any;

type CastMap = StableCastMap<Box<dyn Any>>;

fn main() {
    let map: CastMap = CastMap::new();

    // Insert a concrete type into a dyn Any map.
    let (dog_key, dog_ref) = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    // dog_key: StableCastKey<Dog>
    // dog_ref: &Dog

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
| `StableCastKey<T, Idx, Gen>` | Yes | No — lookups are safe | General use with `StableCastMap` |
| `CastKey<T, Idx, Gen>` | No | Yes — caller must ensure metadata validity | Low-level use with `UnsafeCastMap` |
| `DefaultMapKey<Idx, Gen>` | No | N/A — no metadata | Inner key used by the backing `GenMap` |

`Idx` and `Gen` default to `u32`. Use custom types (e.g. `u16`) for smaller keys.

### Available insert methods

| Method | Key given to closure | Returned key type |
|---|---|---|
| `insert(value)` | — | `StableCastKey<D::Target>` (erased) |
| `insert_with_key(\|inner_key\| ...)` | `DefaultMapKey` | `StableCastKey<D::Target>` (erased) |
| `insert_sized(value)` | — | `StableCastKey<Concrete>` |
| `insert_sized_with_key(\|typed_key\| ...)` | `StableCastKey<Concrete>` | `StableCastKey<Concrete>` |
| `insert_as(value)` | — | `StableCastKey<Source::Target>` |
| `insert_as_with_key(\|inner_key\| ...)` | `DefaultMapKey` | `StableCastKey<Source::Target>` |

### Key upcasting

Since `StableCastKey` stores pointer metadata directly (not inside a `NonNull`), implicit `CoerceUnsized` is not available. Instead, use the `.upcast()` method:

```rust
let concrete_key: StableCastKey<Dog> = map.insert_sized(Box::new(dog)).0;
let erased_key: StableCastKey<dyn Any> = concrete_key.upcast::<dyn Any>();
```

### Clone semantics

When a `StableCastMap` is cloned, the clone receives a **fresh map identity**. Keys from the original are not valid on the clone. Use iteration (`snapshot`, `iter_mut`, `drain`) to obtain new keys for the cloned data.

---

## Comparison to other data structures

`StableGenMap` lives in the same space as generational arenas / slot maps, but it's aimed at a slightly different pattern: **inserting with `&self` while keeping existing `&T` references alive**, in a single-threaded setting where you still sometimes remove elements at well-defined points (e.g. end of a videogame frame).


Rough comparison:

| Crate                             | Insert API                              |             Removals                           |    Main focus            |
|----------------------------------|------------------------------------------|----------------------------|-------------------------------|
| `stable_gen_map::StableGenMap`   | `fn insert(&self, T) -> (K, &T)`         | Yes (But with &mut this time) | Stable `&T` across growth, single-threaded      |
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

## Basic example (using `StableGenMap`)

This shows the main selling point: **insert with `&self`** and indirect references via keys.

```rust
use std::cell::{Cell, RefCell};

use stable_gen_map::key::DefaultKey;
use stable_gen_map::stable_gen_map::StableGenMap;

#[derive(Debug)]
struct Entity {
    key: DefaultKey,
    name: String,
    parent: Cell<Option<DefaultKey>>,
    children: RefCell<Vec<DefaultKey>>,
}

impl Entity {
    /// Add a child *from this entity* using only `&self` and `&StableGenMap`.
    /// Returns both the child's key and a stable `&Entity` reference.
 
    fn add_child<'m>(
        &self,
        map: &'m StableGenMap<DefaultKey, Entity>,
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
        // no need to reget the parent, since the insert did not need &mut
        self.children.borrow_mut().push(child_key);

        (child_key, child_ref)
    }
}

fn main() {
    let mut map: StableGenMap<DefaultKey, Entity> = StableGenMap::new();

    // Create the root entity. We get an `&Entity`, not `&mut Entity`.
    let (root_key, root) = map.insert_with_key(|k| Entity {
        key: k,
        name: "root".into(),
        parent: Cell::new(None),
        children: RefCell::new(Vec::new()),
    });

    // Root spawns a child using only `&self` + `&StableGenMap`.
    let (child_key, child) = root.add_child(&map, "child");

    // That child spawns a grandchild, again only `&self` + `&StableGenMap`.
    let (grandchild_key, grandchild) = child.add_child(&map, "grandchild");

    // Everything stays wired up via generational keys.
    assert_eq!(root.children.borrow().as_slice(), &[child_key]);
    assert_eq!(child.parent.get(), Some(root_key));
    assert_eq!(child.children.borrow().as_slice(), &[grandchild_key]);
    assert_eq!(grandchild.parent.get(), Some(child_key));

    // And the references we got from `add_child` are the same as `get(...)`.
    assert!(std::ptr::eq(child, map.get(child_key).unwrap()));
    assert!(std::ptr::eq(grandchild, map.get(grandchild_key).unwrap()));
}
```
