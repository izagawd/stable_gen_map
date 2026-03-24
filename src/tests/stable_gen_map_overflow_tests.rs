use crate::key::Key;
use crate::stable_map::StableMap;

crate::new_key_type! {
    struct TinyGenKey(u8, u8);
}

#[test]
fn stale_key_after_generation_overflow_is_not_accepted_stable_gen_map() {
    let mut map = StableMap::<TinyGenKey, u32>::new();

    let mut next_value;
    let overflow_key = loop {
        next_value = map.len() as u32;
        let (key, _) = map.insert(next_value);

        if key.data().generation == u8::MAX {
            break key;
        }

        assert_eq!(map.remove(key), Some(next_value));
    };

    // Remove the overflow-generation key
    assert_eq!(map.remove(overflow_key), Some(next_value));
    assert_eq!(map.len(), 0);

    // This is the actual invariant:
    // A removed key must NEVER work again.
    assert!(map.get(overflow_key).is_none());
    assert!(map.get_mut(overflow_key).is_none());

    // Extra sanity: inserting again should not revive the stale key
    let (_new_key, value_ref) = map.insert(999);
    assert_eq!(*value_ref, 999);

    assert!(map.get(overflow_key).is_none());
}
