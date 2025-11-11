#![allow(warnings)]
pub mod stable_deref_gen_map;


pub mod numeric;
pub mod key;
pub mod stable_gen_map;

#[cfg(test)]
mod tests{
    #[cfg(test)]
    mod stable_deref_gen_retain_tests;

    #[cfg(test)]
    mod stable_gen_retain_tests;

    #[cfg(test)]
    mod stable_gen_clone_tests;
    #[cfg(test)]
    mod stable_deref_gen_map_tests;

    #[cfg(test)]
    mod stable_deref_gen_clone_tests;

    #[cfg(test)]
    mod stable_gen_map_tests;

    #[cfg(test)]
    mod stable_gen_snapshot_tests;

    #[cfg(test)]
    mod stable_deref_gen_snapshot_tests;
}

