#![cfg_attr(feature = "castable", feature(ptr_metadata))]
#![cfg_attr(feature = "castable", feature(coerce_unsized))]
#![cfg_attr(feature = "castable", feature(unsize))]

#[cfg(feature = "castable")]
pub mod cast_key;
pub mod gen_map;
pub mod key;
pub mod key_piece;
#[cfg(feature = "castable")]
pub mod map_id;
pub mod slot_item;
#[cfg(feature = "castable")]
pub mod stable_cast_map;
pub mod deref_slot;
pub mod boxed_slot;
#[cfg(feature = "castable")]
pub mod unsafe_cast_map;

#[cfg(feature = "castable")]
pub mod retype_ptr;

#[cfg(test)]
mod tests {
    #[cfg(test)]
    mod stable_deref_gen_retain_tests;

    #[cfg(test)]
    mod stable_gen_retain_tests;

    #[cfg(test)]
    mod stable_deref_gen_map_tests;
    #[cfg(test)]
    mod stable_gen_clone_tests;

    #[cfg(test)]
    mod stable_deref_gen_clone_tests;

    #[cfg(test)]
    mod stable_gen_map_tests;

    #[cfg(test)]
    mod stable_deref_gen_map_overflow_tests;

    #[cfg(test)]
    mod stable_gen_map_overflow_tests;

    #[cfg(test)]
    mod key_macro_tests;

    #[cfg(test)]
    mod stable_gen_snapshot_tests;

    #[cfg(test)]
    mod stable_deref_gen_snapshot_tests;

    #[cfg(test)]
    mod stable_gen_drain_tests;

    #[cfg(test)]
    mod stable_deref_gen_drain_tests;

    #[cfg(all(test, feature = "castable"))]
    mod map_id_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_key_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_map_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_insert_typed_tests;

    #[cfg(test)]
    mod unchecked_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_unchecked_tests;

    #[cfg(test)]
    mod pointer_stability_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_pointer_stability_tests;
}
