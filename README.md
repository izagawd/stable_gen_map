# Stable Generational Map

This Rust library provides a structure, `StableGenMap`, which provides a safe way to insert elements with a `&` reference, rather than a `&mut` reference, in a single threaded environment.
Requiring `&` instead of `&mut` for inserts avoids an exclusive borrow, lowering the incidence of aliasing conflicts enforced by the borrow checker, which may enable more design patterns.

`get` and `remove` are O(1). Insert is O(1) unless there is a resize

It is possible to remove elements with this structure if access to a `&mut` reference is available, which is generally done at events in code such as , for instance, the end of a frame in a videogame

