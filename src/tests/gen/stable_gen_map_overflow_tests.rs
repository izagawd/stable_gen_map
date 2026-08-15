use crate::keys::key::Key;
use crate::slots::boxed_slot::StableGenMap;

crate::new_key_type! {
    struct TinyGenKey(u8, u8);
}

#[test]
fn stale_key_after_generation_overflow_is_not_accepted_stable_gen_map() {
    let mut map = StableGenMap::<TinyGenKey, u32>::new();

    let mut next_value;
    let overflow_key = loop {
        next_value = map.len() as u32;
        let key = map.insert(next_value);

        if key.data().generation() == u8::MAX {
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
    let new_key = map.insert(999);
    let value_ref = map.get(new_key).unwrap();
    assert_eq!(*value_ref, 999);

    assert!(map.get(overflow_key).is_none());
}

// ─── generation-overflow policy: WRAP_ON_OVERFLOW ────────────────────────────

use crate::keys::key::KeyData;

/// A key that opts into wrapping generations on overflow (reuse the slot)
/// instead of the default retire-forever behaviour.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct WrapKey {
    key_data: KeyData<u8, u8>,
}

impl From<KeyData<u8, u8>> for WrapKey {
    fn from(key_data: KeyData<u8, u8>) -> Self {
        Self { key_data }
    }
}

unsafe impl Key for WrapKey {
    type Idx = u8;
    type Gen = u8;
    const WRAP_ON_OVERFLOW: bool = true;
    fn data(&self) -> KeyData<u8, u8> {
        self.key_data
    }
}

#[test]
fn wrapping_key_reuses_slot_and_reissues_generation_on_overflow() {
    let mut map = StableGenMap::<WrapKey, u32>::new();

    // First insert lands in a fresh slot: index 0, generation 1.
    let key_a = map.insert(1000);
    assert_eq!(key_a.data().index(), 0);
    assert_eq!(key_a.data().generation(), 1);
    assert_eq!(map.slots_len(), 1);

    // Cycle that single slot until its generation overflows. Every remove frees
    // it and every insert reuses it, so slots_len stays 1 and the index stays 0.
    let mut last = key_a;
    let mut expected = 1000u32;
    loop {
        let gen = last.data().generation();
        assert_eq!(map.remove(last), Some(expected));
        assert_eq!(map.slots_len(), 1, "slot must be reused, never appended");
        if gen == u8::MAX {
            break; // this remove wrapped the slot's generation back to 0
        }
        last = map.insert(7);
        expected = 7;
        assert_eq!(last.data().index(), 0, "reused the same slot");
    }

    // After the wrap, the next insert reproduces index 0 / generation 1: the
    // exact key value handed out at the very beginning.
    let revived = map.insert(2222);
    assert_eq!(revived.data().index(), 0);
    assert_eq!(revived.data().generation(), 1);
    assert_eq!(revived, key_a);
    assert_eq!(map.slots_len(), 1);

    // ABA hazard, memory-safe and documented: the stale key_a now resolves to
    // the NEW value, because wrapping reused its generation.
    assert_eq!(map.get(key_a), Some(&2222));
}

#[test]
fn retiring_key_does_not_reuse_slot_on_overflow() {
    // TinyGenKey (from new_key_type!) uses the default WRAP_ON_OVERFLOW = false.
    let mut map = StableGenMap::<TinyGenKey, u32>::new();

    let key_a = map.insert(1000);
    assert_eq!(key_a.data().index(), 0);
    assert_eq!(key_a.data().generation(), 1);

    // Cycle the single slot until overflow retires it.
    let mut last = key_a;
    loop {
        let gen = last.data().generation();
        map.remove(last);
        if gen == u8::MAX {
            break; // retires slot 0 (generation 0, left off the free list)
        }
        last = map.insert(0);
        assert_eq!(last.data().index(), 0);
    }

    // The retired slot is NOT reused: the next insert appends a brand-new slot.
    let after = map.insert(2222);
    assert_eq!(after.data().index(), 1, "retired slot must not be reused");
    assert_eq!(map.slots_len(), 2);

    // The stale key stays dead forever. `after` also has generation 1, but it
    // sits at a different index, so there is no collision and no ABA.
    assert_eq!(after.data().generation(), 1);
    assert!(map.get(key_a).is_none());
}
