use crate::key::Key;
use crate::stable_deref_gen_map::BoxStableDerefMap;

crate::new_key_type! {
    struct TinyDerefGenKey(u8, u8);
}

use std::panic::{catch_unwind, AssertUnwindSafe};

use crate::stable_gen_map::StableMap;

crate::new_key_type! {
    struct TinyGenKey(u8, u8);
}

#[test]
fn stable_gen_map_into_iter_handles_max_live_generation_without_panicking() {
    let mut map = StableMap::<TinyGenKey, u32>::new();

    loop {
        let next_value = map.len() as u32;
        let (key, _) = map.insert(next_value);

        if key.data().generation == u8::MAX {
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
fn stale_key_after_generation_overflow_is_not_accepted_stable_deref_gen_map() {
    let mut map = BoxStableDerefMap::<TinyDerefGenKey, u32>::new();
    let mut next_value;
    let overflow_key = loop {
        next_value = map.len() as u32;
        let (key, _) = map.insert(Box::new(next_value));

        if key.data().generation == u8::MAX {
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
    let (_new_key, value_ref) = map.insert(Box::new(999));
    assert_eq!(*value_ref, 999);

    assert!(map.get(overflow_key).is_none());
}
