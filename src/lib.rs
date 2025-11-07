pub mod stable_gen_map;
pub mod paged_stable_gen_map;

pub mod numeric;
pub mod key;
mod tests{

    #[cfg(test)]
    mod stable_gen_map_tests;

    #[cfg(test)]
    mod stable_gen_clone_tests;

    #[cfg(test)]
    mod paged_stable_gen_map_tests;

    #[cfg(test)]
    mod snapshop_paged_test;

    #[cfg(test)]
    mod snapshot_stable_gen_test;
}

