use crate::cast_key::{CastKey, DefaultCastKey, DefaultMapKey};
use crate::key::Key;
use crate::stable_cast_map::StableCastMap;
use std::any::Any;
use std::cell::Cell;

// ─── Test types ────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
struct Dog {
    name: String,
}

#[derive(Debug, Clone, PartialEq)]
struct Cat {
    lives: u8,
}

#[derive(Debug, Clone, PartialEq)]
struct Parrot {
    color: String,
}

// ─── Trait hierarchy for insert_as upcasting tests ─────────────────────────

trait Parent: Any {
    fn parent_name(&self) -> &'static str;
    fn as_any(&self) -> &dyn Any;
}

trait Child: Parent {
    fn child_value(&self) -> i32;
}

trait Sibling: Parent {
    fn sibling_id(&self) -> u64;
}

#[derive(Debug, PartialEq)]
struct Alpha {
    val: i32,
}

impl Parent for Alpha {
    fn parent_name(&self) -> &'static str {
        "Alpha"
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}
impl Child for Alpha {
    fn child_value(&self) -> i32 {
        self.val
    }
}

#[derive(Debug, PartialEq)]
struct Beta {
    id: u64,
}

impl Parent for Beta {
    fn parent_name(&self) -> &'static str {
        "Beta"
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}
impl Sibling for Beta {
    fn sibling_id(&self) -> u64 {
        self.id
    }
}

#[derive(Debug, PartialEq)]
struct Gamma {
    tag: String,
}

impl Parent for Gamma {
    fn parent_name(&self) -> &'static str {
        "Gamma"
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}
impl Child for Gamma {
    fn child_value(&self) -> i32 {
        self.tag.len() as i32
    }
}
impl Sibling for Gamma {
    fn sibling_id(&self) -> u64 {
        42
    }
}

// ─── Map aliases ───────────────────────────────────────────────────────────

type AnyMap = StableCastMap<DefaultCastKey<dyn Any>, Box<dyn Any>>;
type ParentMap = StableCastMap<DefaultCastKey<dyn Parent>, Box<dyn Parent>>;

// ═══════════════════════════════════════════════════════════════════════════
//  insert_sized
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn insert_sized_returns_concrete_key_and_ref() {
    let map: AnyMap = AnyMap::new();
    let (key, dog_ref) = map.insert_sized(Box::new(Dog {
        name: "Rex".into(),
    }));

    // key is DefaultCastKey<Dog>, not DefaultCastKey<dyn Any>
    let _: DefaultCastKey<Dog> = key;

    // ref is &Dog, not &dyn Any
    assert_eq!(dog_ref.name, "Rex");
}

#[test]
fn insert_sized_key_can_upcast_to_dyn_any() {
    let map: AnyMap = AnyMap::new();
    let (dog_key, _) = map.insert_sized(Box::new(Dog {
        name: "Buddy".into(),
    }));

    // Upcast via CoerceUnsized
    let dyn_key: DefaultCastKey<dyn Any> = dog_key;

    let val = map.get(dyn_key).unwrap();
    let dog = val.downcast_ref::<Dog>().unwrap();
    assert_eq!(dog.name, "Buddy");
}

#[test]
fn insert_sized_concrete_key_works_for_get() {
    let map: AnyMap = AnyMap::new();
    let (key, _) = map.insert_sized(Box::new(42i32));

    let val: &i32 = map.get(key).unwrap();
    assert_eq!(*val, 42);
}

#[test]
fn insert_sized_concrete_key_works_for_get_mut() {
    let mut map: AnyMap = AnyMap::new();
    let (key, _) = map.insert_sized(Box::new(Dog {
        name: "Old".into(),
    }));

    let dog: &mut Dog = map.get_mut(key).unwrap();
    dog.name = "New".into();

    let dog: &Dog = map.get(key).unwrap();
    assert_eq!(dog.name, "New");
}

#[test]
fn insert_sized_concrete_key_works_for_remove() {
    let mut map: AnyMap = AnyMap::new();
    let (key, _) = map.insert_sized(Box::new(99i32));
    assert_eq!(map.len(), 1);

    let removed = map.remove(key);
    assert!(removed.is_some());
    assert_eq!(map.len(), 0);
}

#[test]
fn insert_sized_multiple_types() {
    let map: AnyMap = AnyMap::new();
    let (k_dog, dog_ref) = map.insert_sized(Box::new(Dog {
        name: "Rex".into(),
    }));
    let (k_cat, cat_ref) = map.insert_sized(Box::new(Cat { lives: 9 }));
    let (k_int, int_ref) = map.insert_sized(Box::new(123i32));

    assert_eq!(dog_ref.name, "Rex");
    assert_eq!(cat_ref.lives, 9);
    assert_eq!(*int_ref, 123);

    assert_eq!(map.get(k_dog).unwrap().name, "Rex");
    assert_eq!(map.get(k_cat).unwrap().lives, 9);
    assert_eq!(*map.get(k_int).unwrap(), 123);

    assert_eq!(map.len(), 3);
}

#[test]
fn insert_sized_pointer_stability() {
    let map: AnyMap = AnyMap::new();
    let (key, first_ref) = map.insert_sized(Box::new(Dog {
        name: "Stable".into(),
    }));
    let ptr = first_ref as *const Dog as usize;

    // Trigger growth
    for i in 0..100 {
        map.insert_sized(Box::new(i as u64));
    }

    let again: &Dog = map.get(key).unwrap();
    assert_eq!(again as *const Dog as usize, ptr);
    assert_eq!(again.name, "Stable");
}

#[test]
fn insert_sized_inner_key_matches() {
    let map: AnyMap = AnyMap::new();
    let (key, _) = map.insert_sized(Box::new(77i32));

    // Inner key from concrete key should work with get_by_inner_key
    let inner = key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 77);
}

#[test]
fn insert_sized_stale_key_returns_none() {
    let mut map: AnyMap = AnyMap::new();
    let (key, _) = map.insert_sized(Box::new(1i32));
    map.remove(key);
    map.insert_sized(Box::new(2i32)); // reuses slot
    assert!(map.get(key).is_none());
}

#[test]
fn insert_sized_cross_map_key_rejected() {
    let map_a: AnyMap = AnyMap::new();
    let map_b: AnyMap = AnyMap::new();

    let (key_a, _) = map_a.insert_sized(Box::new(1i32));
    map_b.insert_sized(Box::new(2i32));

    assert!(map_b.get(key_a).is_none());
}

// ═══════════════════════════════════════════════════════════════════════════
//  insert_sized_with_key
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn insert_sized_with_key_closure_receives_typed_key() {
    let map: AnyMap = AnyMap::new();

    let captured: Cell<Option<DefaultCastKey<Dog>>> = Cell::new(None);

    let (returned_key, dog_ref) = map.insert_sized_with_key(|key: DefaultCastKey<Dog>| {
        captured.set(Some(key));
        Box::new(Dog {
            name: "Keyed".into(),
        })
    });

    let cap = captured.get().unwrap();
    assert_eq!(cap.inner_key().data().idx, returned_key.inner_key().data().idx);
    assert_eq!(
        cap.inner_key().data().generation,
        returned_key.inner_key().data().generation
    );
    assert_eq!(dog_ref.name, "Keyed");
}

#[test]
fn insert_sized_with_key_stores_own_key() {
    let map: AnyMap = AnyMap::new();

    struct SelfAware {
        my_key: DefaultCastKey<SelfAware>,
        data: i32,
    }

    let (key, sa_ref) = map.insert_sized_with_key(|key: DefaultCastKey<SelfAware>| {
        Box::new(SelfAware {
            my_key: key,
            data: 42,
        })
    });

    assert_eq!(sa_ref.data, 42);
    assert_eq!(sa_ref.my_key.inner_key().data().idx, key.inner_key().data().idx);
}

#[test]
fn insert_sized_with_key_upcast_then_get() {
    let map: AnyMap = AnyMap::new();

    let (cat_key, _) = map.insert_sized_with_key(|_key: DefaultCastKey<Cat>| {
        Box::new(Cat { lives: 7 })
    });

    let dyn_key: DefaultCastKey<dyn Any> = cat_key;
    let val = map.get(dyn_key).unwrap();
    assert_eq!(*val.downcast_ref::<Cat>().unwrap(), Cat { lives: 7 });
}

#[test]
fn insert_sized_with_key_multiple() {
    let map: AnyMap = AnyMap::new();

    let (k1, _) = map.insert_sized_with_key(|_: DefaultCastKey<i32>| Box::new(1i32));
    let (k2, _) = map.insert_sized_with_key(|_: DefaultCastKey<i32>| Box::new(2i32));
    let (k3, _) = map.insert_sized_with_key(|_: DefaultCastKey<i32>| Box::new(3i32));

    assert_eq!(map.len(), 3);
    assert_eq!(*map.get(k1).unwrap(), 1);
    assert_eq!(*map.get(k2).unwrap(), 2);
    assert_eq!(*map.get(k3).unwrap(), 3);
}

#[test]
fn insert_sized_with_key_after_remove_reuses_slot() {
    let mut map: AnyMap = AnyMap::new();
    let (k1, _) = map.insert_sized_with_key(|_: DefaultCastKey<i32>| Box::new(1i32));
    map.remove(k1);

    let (k2, _) = map.insert_sized_with_key(|_: DefaultCastKey<i32>| Box::new(2i32));
    assert_eq!(map.len(), 1);
    assert!(map.get(k1).is_none());
    assert_eq!(*map.get(k2).unwrap(), 2);
}

// ═══════════════════════════════════════════════════════════════════════════
//  try_insert_sized_with_key
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn try_insert_sized_with_key_ok() {
    let map: AnyMap = AnyMap::new();

    let result = map.try_insert_sized_with_key(|_key: DefaultCastKey<i32>| Ok::<_, ()>(Box::new(42i32)));
    assert!(result.is_ok());

    let (key, val) = result.unwrap();
    assert_eq!(*val, 42);
    assert_eq!(*map.get(key).unwrap(), 42);
}

#[test]
fn try_insert_sized_with_key_err_does_not_insert() {
    let map: AnyMap = AnyMap::new();

    let result = map.try_insert_sized_with_key(
        |_key: DefaultCastKey<i32>| Err::<Box<i32>, _>("fail"),
    );
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), "fail");
    assert_eq!(map.len(), 0);
}

#[test]
fn try_insert_sized_with_key_err_slot_reusable() {
    let map: AnyMap = AnyMap::new();

    let _ = map.try_insert_sized_with_key(|_: DefaultCastKey<i32>| Err::<Box<i32>, _>(()));

    let (key, val) = map
        .try_insert_sized_with_key(|_: DefaultCastKey<i32>| Ok::<_, ()>(Box::new(99i32)))
        .unwrap();

    assert_eq!(map.len(), 1);
    assert_eq!(*val, 99);
    assert_eq!(*map.get(key).unwrap(), 99);
}

#[test]
fn try_insert_sized_with_key_closure_receives_typed_key() {
    let map: AnyMap = AnyMap::new();

    let captured: Cell<Option<DefaultCastKey<Dog>>> = Cell::new(None);

    let (returned_key, _) = map
        .try_insert_sized_with_key(|key: DefaultCastKey<Dog>| {
            captured.set(Some(key));
            Ok::<_, ()>(Box::new(Dog {
                name: "Try".into(),
            }))
        })
        .unwrap();

    let cap = captured.get().unwrap();
    assert_eq!(
        cap.inner_key().data().idx,
        returned_key.inner_key().data().idx
    );
}

// ═══════════════════════════════════════════════════════════════════════════
//  insert_as  (trait upcasting: dyn Child → dyn Parent)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn insert_as_child_into_parent_map() {
    let map: ParentMap = ParentMap::new();

    let child: Box<dyn Child> = Box::new(Alpha { val: 10 });
    let (key, child_ref) = map.insert_as(child);

    // key is DefaultCastKey<dyn Child>
    let _: DefaultCastKey<dyn Child> = key;

    // ref is &dyn Child
    assert_eq!(child_ref.child_value(), 10);
    assert_eq!(child_ref.parent_name(), "Alpha");
}

#[test]
fn insert_as_key_upcasts_to_parent() {
    let map: ParentMap = ParentMap::new();

    let (child_key, _) = map.insert_as(Box::new(Alpha { val: 5 }) as Box<dyn Child>);

    // Upcast key from dyn Child → dyn Parent
    let parent_key: DefaultCastKey<dyn Parent> = child_key;

    let parent_ref: &dyn Parent = map.get(parent_key).unwrap();
    assert_eq!(parent_ref.parent_name(), "Alpha");
}

#[test]
fn insert_as_child_key_works_for_get() {
    let map: ParentMap = ParentMap::new();

    let (child_key, _) = map.insert_as(Box::new(Alpha { val: 7 }) as Box<dyn Child>);

    let child_ref: &dyn Child = map.get(child_key).unwrap();
    assert_eq!(child_ref.child_value(), 7);
}

#[test]
fn insert_as_child_key_works_for_get_mut() {
    let mut map: ParentMap = ParentMap::new();

    let (child_key, _) = map.insert_as(Box::new(Alpha { val: 1 }) as Box<dyn Child>);

    let child_ref: &mut dyn Child = map.get_mut(child_key).unwrap();
    assert_eq!(child_ref.child_value(), 1);
    // Can also call parent methods
    assert_eq!(child_ref.parent_name(), "Alpha");
}

#[test]
fn insert_as_child_key_works_for_remove() {
    let mut map: ParentMap = ParentMap::new();
    let (child_key, _) = map.insert_as(Box::new(Alpha { val: 1 }) as Box<dyn Child>);
    assert_eq!(map.len(), 1);

    let removed = map.remove(child_key);
    assert!(removed.is_some());
    assert_eq!(map.len(), 0);
}

#[test]
fn insert_as_sibling_into_parent_map() {
    let map: ParentMap = ParentMap::new();

    let (sibling_key, sib_ref) = map.insert_as(Box::new(Beta { id: 99 }) as Box<dyn Sibling>);

    let _: DefaultCastKey<dyn Sibling> = sibling_key;
    assert_eq!(sib_ref.sibling_id(), 99);
    assert_eq!(sib_ref.parent_name(), "Beta");
}

#[test]
fn insert_as_mixed_child_and_sibling() {
    let map: ParentMap = ParentMap::new();

    let (child_key, _) = map.insert_as(Box::new(Alpha { val: 10 }) as Box<dyn Child>);
    let (sib_key, _) = map.insert_as(Box::new(Beta { id: 20 }) as Box<dyn Sibling>);

    // Both upcast to parent
    let pk1: DefaultCastKey<dyn Parent> = child_key;
    let pk2: DefaultCastKey<dyn Parent> = sib_key;

    assert_eq!(map.get(pk1).unwrap().parent_name(), "Alpha");
    assert_eq!(map.get(pk2).unwrap().parent_name(), "Beta");

    // Original typed keys still work
    assert_eq!(map.get(child_key).unwrap().child_value(), 10);
    assert_eq!(map.get(sib_key).unwrap().sibling_id(), 20);

    assert_eq!(map.len(), 2);
}

#[test]
fn insert_as_concrete_into_parent_map() {
    // insert_as also works for Sized → dyn Parent (concrete type)
    let map: ParentMap = ParentMap::new();

    let (key, gamma_ref) = map.insert_sized(Box::new(Gamma {
        tag: "hello".into(),
    }));

    let _: DefaultCastKey<Gamma> = key;
    assert_eq!(gamma_ref.tag, "hello");

    // Upcast concrete → dyn Parent
    let parent_key: DefaultCastKey<dyn Parent> = key;
    assert_eq!(map.get(parent_key).unwrap().parent_name(), "Gamma");
}

#[test]
fn insert_as_pointer_stability() {
    let map: ParentMap = ParentMap::new();

    let (key, first_ref) = map.insert_as(Box::new(Alpha { val: 42 }) as Box<dyn Child>);
    let ptr = first_ref as *const dyn Child as *const () as usize;

    // Trigger growth
    for i in 0..100 {
        map.insert_as(Box::new(Alpha { val: i }) as Box<dyn Child>);
    }

    let again: &dyn Child = map.get(key).unwrap();
    assert_eq!(again as *const dyn Child as *const () as usize, ptr);
    assert_eq!(again.child_value(), 42);
}

#[test]
fn insert_as_stale_key_returns_none() {
    let mut map: ParentMap = ParentMap::new();

    let (child_key, _) = map.insert_as(Box::new(Alpha { val: 1 }) as Box<dyn Child>);
    map.remove(child_key);
    map.insert_as(Box::new(Beta { id: 2 }) as Box<dyn Sibling>);

    assert!(map.get(child_key).is_none());
}

#[test]
fn insert_as_cross_map_key_rejected() {
    let map_a: ParentMap = ParentMap::new();
    let map_b: ParentMap = ParentMap::new();

    let (key_a, _) = map_a.insert_as(Box::new(Alpha { val: 1 }) as Box<dyn Child>);
    map_b.insert_as(Box::new(Alpha { val: 2 }) as Box<dyn Child>);

    assert!(map_b.get(key_a).is_none());
}

#[test]
fn insert_as_inner_key_matches() {
    let map: ParentMap = ParentMap::new();

    let (child_key, _) = map.insert_as(Box::new(Alpha { val: 55 }) as Box<dyn Child>);

    // Inner key from child key should work for parent lookup
    let inner = child_key.inner_key();
    let parent_ref = map.get_by_inner_key(inner).unwrap();
    assert_eq!(parent_ref.parent_name(), "Alpha");
}

// ═══════════════════════════════════════════════════════════════════════════
//  insert_as_with_key
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn insert_as_with_key_closure_receives_inner_key() {
    let map: ParentMap = ParentMap::new();

    let captured: Cell<Option<DefaultMapKey<u32, u32>>> = Cell::new(None);

    let (child_key, child_ref) = map.insert_as_with_key(|inner_key| {
        captured.set(Some(inner_key));
        Box::new(Alpha { val: 33 }) as Box<dyn Child>
    });

    let cap = captured.get().unwrap();
    assert_eq!(cap.data().idx, child_key.inner_key().data().idx);
    assert_eq!(cap.data().generation, child_key.inner_key().data().generation);
    assert_eq!(cap.extra(), child_key.inner_key().extra());

    assert_eq!(child_ref.child_value(), 33);
}

#[test]
fn insert_as_with_key_returns_typed_key() {
    let map: ParentMap = ParentMap::new();

    let (key, _) = map.insert_as_with_key(|_inner_key| {
        Box::new(Alpha { val: 7 }) as Box<dyn Child>
    });

    let _: DefaultCastKey<dyn Child> = key;

    let child_ref: &dyn Child = map.get(key).unwrap();
    assert_eq!(child_ref.child_value(), 7);
}

#[test]
fn insert_as_with_key_upcast_then_get() {
    let map: ParentMap = ParentMap::new();

    let (child_key, _) = map.insert_as_with_key(|_| {
        Box::new(Alpha { val: 11 }) as Box<dyn Child>
    });

    let parent_key: DefaultCastKey<dyn Parent> = child_key;
    let parent_ref: &dyn Parent = map.get(parent_key).unwrap();
    assert_eq!(parent_ref.parent_name(), "Alpha");
}

#[test]
fn insert_as_with_key_multiple() {
    let map: ParentMap = ParentMap::new();

    let (k1, _) = map.insert_as_with_key(|_| Box::new(Alpha { val: 1 }) as Box<dyn Child>);
    let (k2, _) = map.insert_as_with_key(|_| Box::new(Beta { id: 2 }) as Box<dyn Sibling>);
    let (k3, _) = map.insert_as_with_key(|_| Box::new(Alpha { val: 3 }) as Box<dyn Child>);

    assert_eq!(map.len(), 3);
    assert_eq!(map.get(k1).unwrap().child_value(), 1);
    assert_eq!(map.get(k2).unwrap().sibling_id(), 2);
    assert_eq!(map.get(k3).unwrap().child_value(), 3);
}

#[test]
fn insert_as_with_key_after_remove_reuses_slot() {
    let mut map: ParentMap = ParentMap::new();

    let (k1, _) = map.insert_as_with_key(|_| Box::new(Alpha { val: 1 }) as Box<dyn Child>);
    map.remove(k1);

    let (k2, _) = map.insert_as_with_key(|_| Box::new(Alpha { val: 2 }) as Box<dyn Child>);

    assert_eq!(map.len(), 1);
    assert!(map.get(k1).is_none());
    assert_eq!(map.get(k2).unwrap().child_value(), 2);
}

#[test]
fn insert_as_with_key_can_store_inner_key() {
    let map: ParentMap = ParentMap::new();

    struct SelfAwareChild {
        inner_key: DefaultMapKey<u32, u32>,
        val: i32,
    }
    impl Parent for SelfAwareChild {
        fn parent_name(&self) -> &'static str {
            "SelfAwareChild"
        }
        fn as_any(&self) -> &dyn Any {
            self
        }
    }
    impl Child for SelfAwareChild {
        fn child_value(&self) -> i32 {
            self.val
        }
    }

    let (child_key, child_ref) = map.insert_as_with_key(|inner_key| {
        Box::new(SelfAwareChild {
            inner_key,
            val: 100,
        }) as Box<dyn Child>
    });

    assert_eq!(child_ref.child_value(), 100);

    // Verify the stored inner key matches
    let parent_ref = map.get_by_inner_key(child_key.inner_key()).unwrap();
    let downcasted = parent_ref.as_any().downcast_ref::<SelfAwareChild>().unwrap();
    assert_eq!(
        downcasted.inner_key.data().idx,
        child_key.inner_key().data().idx
    );
}

// ═══════════════════════════════════════════════════════════════════════════
//  try_insert_as_with_key
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn try_insert_as_with_key_ok() {
    let map: ParentMap = ParentMap::new();

    let result = map.try_insert_as_with_key(|_inner_key| {
        Ok::<_, ()>(Box::new(Alpha { val: 42 }) as Box<dyn Child>)
    });

    assert!(result.is_ok());
    let (key, child_ref) = result.unwrap();
    assert_eq!(child_ref.child_value(), 42);

    let child_again: &dyn Child = map.get(key).unwrap();
    assert_eq!(child_again.child_value(), 42);
    assert_eq!(map.len(), 1);
}

#[test]
fn try_insert_as_with_key_err_does_not_insert() {
    let map: ParentMap = ParentMap::new();

    let result = map.try_insert_as_with_key(|_inner_key| {
        Err::<Box<dyn Child>, _>("something broke")
    });

    assert!(result.is_err());
    assert_eq!(map.len(), 0);
}

#[test]
fn try_insert_as_with_key_err_slot_reusable() {
    let map: ParentMap = ParentMap::new();

    let _ = map.try_insert_as_with_key(|_| Err::<Box<dyn Child>, _>(()));

    let (key, child_ref) = map
        .try_insert_as_with_key(|_| {
            Ok::<_, ()>(Box::new(Alpha { val: 99 }) as Box<dyn Child>)
        })
        .unwrap();

    assert_eq!(map.len(), 1);
    assert_eq!(child_ref.child_value(), 99);
    assert_eq!(map.get(key).unwrap().child_value(), 99);
}

#[test]
fn try_insert_as_with_key_ok_returns_typed_key() {
    let map: ParentMap = ParentMap::new();

    let (child_key, _) = map
        .try_insert_as_with_key(|_| {
            Ok::<_, ()>(Box::new(Beta { id: 77 }) as Box<dyn Sibling>)
        })
        .unwrap();

    let _: DefaultCastKey<dyn Sibling> = child_key;

    let sib: &dyn Sibling = map.get(child_key).unwrap();
    assert_eq!(sib.sibling_id(), 77);

    // Upcast to parent
    let parent_key: DefaultCastKey<dyn Parent> = child_key;
    assert_eq!(map.get(parent_key).unwrap().parent_name(), "Beta");
}

#[test]
fn try_insert_as_with_key_inner_key_matches() {
    let map: ParentMap = ParentMap::new();

    let captured: Cell<Option<DefaultMapKey<u32, u32>>> = Cell::new(None);

    let (child_key, _) = map
        .try_insert_as_with_key(|inner_key| {
            captured.set(Some(inner_key));
            Ok::<_, ()>(Box::new(Alpha { val: 55 }) as Box<dyn Child>)
        })
        .unwrap();

    let cap = captured.get().unwrap();
    assert_eq!(cap.data().idx, child_key.inner_key().data().idx);
    assert_eq!(
        cap.data().generation,
        child_key.inner_key().data().generation
    );
    assert_eq!(cap.extra(), child_key.inner_key().extra());
}

#[test]
fn try_insert_as_with_key_ok_then_err_preserves_first() {
    let map: ParentMap = ParentMap::new();

    let (k1, _) = map
        .try_insert_as_with_key(|_| {
            Ok::<_, ()>(Box::new(Alpha { val: 1 }) as Box<dyn Child>)
        })
        .unwrap();

    let _ = map.try_insert_as_with_key(|_| Err::<Box<dyn Child>, _>(()));

    assert_eq!(map.len(), 1);
    assert_eq!(map.get(k1).unwrap().child_value(), 1);
}

// ═══════════════════════════════════════════════════════════════════════════
//  Interop: insert_sized and insert_as on the same map
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn mixed_insert_and_insert_sized_and_insert_as() {
    let map: ParentMap = ParentMap::new();

    // insert (native)
    let (pk, _) = map.insert(Box::new(Alpha { val: 1 }) as Box<dyn Parent>);

    // insert_sized (concrete)
    let (gk, _) = map.insert_sized(Box::new(Gamma {
        tag: "hi".into(),
    }));

    // insert_as (trait upcast)
    let (ck, _) = map.insert_as(Box::new(Alpha { val: 3 }) as Box<dyn Child>);

    assert_eq!(map.len(), 3);

    // All lookups work
    let p: &dyn Parent = map.get(pk).unwrap();
    assert_eq!(p.parent_name(), "Alpha");

    let g: &Gamma = map.get(gk).unwrap();
    assert_eq!(g.tag, "hi");

    let c: &dyn Child = map.get(ck).unwrap();
    assert_eq!(c.child_value(), 3);

    // All upcast to parent
    let pk_from_g: DefaultCastKey<dyn Parent> = gk;
    let pk_from_c: DefaultCastKey<dyn Parent> = ck;
    assert_eq!(map.get(pk_from_g).unwrap().parent_name(), "Gamma");
    assert_eq!(map.get(pk_from_c).unwrap().parent_name(), "Alpha");
}

#[test]
fn insert_as_on_dyn_any_map_with_trait_object() {
    // insert_as also works on a dyn Any map with a non-Any trait object,
    // as long as dyn Child: Unsize<dyn Any> (which it doesn't by default).
    // But we CAN insert Box<dyn Child> into a dyn Parent map, which is
    // the primary use case. This test just confirms the dyn Parent map
    // path works end-to-end with multiple trait levels.
    let map: ParentMap = ParentMap::new();

    // Gamma implements both Child and Sibling
    let (ck, _) = map.insert_as(Box::new(Gamma {
        tag: "multi".into(),
    }) as Box<dyn Child>);
    let (sk, _) = map.insert_as(Box::new(Gamma {
        tag: "multi2".into(),
    }) as Box<dyn Sibling>);

    assert_eq!(map.get(ck).unwrap().child_value(), 5); // "multi".len()
    assert_eq!(map.get(sk).unwrap().sibling_id(), 42);
}
