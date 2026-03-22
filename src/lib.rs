#![allow(warnings)]
#![feature(ptr_metadata)]
pub mod gen_map;
pub mod castable_map;
pub mod key;
pub mod key_castable;
pub mod key_piece;
pub mod map_id;
pub mod slot_item;
pub mod stable_deref_gen_map;
pub mod stable_gen_map;

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
}
