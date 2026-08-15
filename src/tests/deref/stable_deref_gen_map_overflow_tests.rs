use crate::keys::key::Key;
use crate::slots::deref_slot::BoxStableDerefMap;

crate::new_key_type! {
    struct TinyDerefGenKey(u8, u8);
}

use std::panic::{catch_unwind, AssertUnwindSafe};

use crate::slots::boxed_slot::StableGenMap;

crate::new_key_type! {
    struct TinyGenKey(u8, u8);
}

#[test]
fn stable_gen_map_into_iter_handles_max_live_generation_without_panicking() {
    let mut map = StableGenMap::<TinyGenKey, u32>::new();

    loop {
        let next_value = map.len() as u32;
        let key = map.insert(next_value);

        if key.data().generation() == u8::MAX {
            break;
        }

        assert_eq!(map.remove(key), Some(next_value));
    }

    let result = catch_unwind(AssertUnwindSafe(|| {
        let mut iter = map.into_iter();

        iter.next()
            .map(|(key, value)| (key.data().generation, value));

        assert_eq!(iter.next(), None);
    }));

    assert!(
        result.is_ok(),
        "into_iter should not panic when consuming a slot at the max live generation",
    );
}

#[test]
fn clear_after_generation_overflow_does_not_panic() {
    let mut map = StableGenMap::<TinyGenKey, u32>::new();

    // Cycle a single slot until its generation overflows and retires (gen = 0)
    loop {
        let key = map.insert(42);
        if key.data().generation() == u8::MAX {
            map.remove(key); // this overflow-retires the slot (sets gen to 0)
            break;
        }
        map.remove(key);
    }

    // Insert a second value so the map isn't empty
    let k2 = map.insert(99);
    assert_eq!(map.len(), 1);

    // clear() must not UB/panic when iterating over the retired slot
    map.clear();
    assert_eq!(map.len(), 0);
    assert!(map.get(k2).is_none());
}

#[test]
fn stale_key_after_generation_overflow_is_not_accepted_stable_deref_gen_map() {
    let mut map = BoxStableDerefMap::<TinyDerefGenKey, u32>::new();
    let mut next_value;
    let overflow_key = loop {
        next_value = map.len() as u32;
        let key = map.insert(Box::new(next_value));

        if key.data().generation() == u8::MAX {
            break key;
        }

        assert_eq!(map.remove(key).map(|b| *b), Some(next_value));
    };

    // Remove the overflow-generation key
    assert_eq!(map.remove(overflow_key).map(|b| *b), Some(next_value));
    assert_eq!(map.len(), 0);

    // Core invariant: stale key must be dead
    assert!(map.get(overflow_key).is_none());
    assert!(map.get_mut(overflow_key).is_none());

    // Ensure reinsertion doesn't revive it
    let new_key = map.insert(Box::new(999));
    let value_ref = map.get(new_key).unwrap();
    assert_eq!(*value_ref, 999);

    assert!(map.get(overflow_key).is_none());
}

// ─── generation-overflow policy: WRAP_ON_OVERFLOW (deref storage) ─────────────

use crate::keys::key::KeyData;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct WrapDerefKey {
    key_data: KeyData<u8, u8>,
}

impl From<KeyData<u8, u8>> for WrapDerefKey {
    fn from(key_data: KeyData<u8, u8>) -> Self {
        Self { key_data }
    }
}

unsafe impl Key for WrapDerefKey {
    type Idx = u8;
    type Gen = u8;
    const WRAP_ON_OVERFLOW: bool = true;
    fn data(&self) -> KeyData<u8, u8> {
        self.key_data
    }
}

#[test]
fn wrapping_key_reuses_slot_on_overflow_deref() {
    let mut map = BoxStableDerefMap::<WrapDerefKey, u32>::new();

    let key_a = map.insert(Box::new(1000));
    assert_eq!(key_a.data().index(), 0);
    assert_eq!(key_a.data().generation(), 1);
    assert_eq!(map.slots_len(), 1);

    let mut last = key_a;
    let mut expected = 1000u32;
    loop {
        let gen = last.data().generation();
        assert_eq!(map.remove(last).map(|b| *b), Some(expected));
        assert_eq!(map.slots_len(), 1, "slot must be reused, never appended");
        if gen == u8::MAX {
            break;
        }
        last = map.insert(Box::new(7));
        expected = 7;
        assert_eq!(last.data().index(), 0);
    }

    // Wrapped back around to the very first key value.
    let revived = map.insert(Box::new(2222));
    assert_eq!(revived, key_a);
    assert_eq!(map.slots_len(), 1);

    // ABA hazard, memory-safe: stale key_a resolves to the new deref target.
    assert_eq!(map.get(key_a), Some(&2222));
}
