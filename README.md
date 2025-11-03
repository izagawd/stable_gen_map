# Stable Generational Map

This Rust library provides a structure, `StableGenMap`, which provides a safe way to insert elements with a `&` reference, rather than a `&mut` reference, in a single threaded environment.

Requiring `&` instead of `&mut` for inserts avoids an exclusive borrow, lowering the incidence of aliasing conflicts enforced by the borrow checker, which may enable more design patterns.

`get` and `remove` are O(1). Insert is O(1) unless there is a resize.

It is possible to remove elements with this structure if access to a `&mut` reference is available, which is generally done at events in code such as, for instance, the end of a frame in a videogame.

# Example

```rust
struct Human{
    name: String,
    age: Cell<u8>,
    friend: Cell<Option<DefaultKey>> // custom keys can be made,
}

let map = StableGenMap::<DefaultKey /* custom keys can be made */,Human>::new();

// insert requires &, not &mut
let (drake_key, drake_reference) = map.insert(Box::new(Human{
    age: Cell::new(20),
    name: String::from("Drake"),
    friend: Cell::new(None),
}));

```

another example

```rust
// Now, we want to store reference of the key in self.

struct Human{
    name: String,
    age: Cell<u8>,
    friend: Cell<Option<DefaultKey>> // custom keys can be made,
}

struct HumanWithKey{
    human: Human,
    key: DefaultKey,
}

impl HumanWithKey{
    fn make_new_friend(&self, map: &StableGenMap<DefaultKey,HumanWithKey>){
        // insert requires &, not &mut
        let (key, reference) =  map.insert_with(|key| Box::new( HumanWithKey{
            human: Human{
                age: Cell::new(21),
                name: String::from("John"),
                friend: Cell::new(Some(self.key))
            },
            key,
        }));
        self.human.friend.set(Some(key));
    }
}

// Again, requires &, not &mut
let map_human_with_key = StableGenMap::<DefaultKey, HumanWithKey>::new();
let (damian_key, damian_reference) = map_human_with_key.insert_with(|key| Box::new(HumanWithKey{
    human: Human{
        name: String::from("Damian"),
        age: Cell::new(40),
        friend: Cell::new(None)
    },
    key,
}));

damian_reference.make_new_friend(&map_human_with_key);

let damian_friend_key = damian_reference.human.friend.get().unwrap();
assert_eq!(damian_key, map_human_with_key[damian_friend_key].human.friend.get().unwrap());
```

# License

This rust crate uses the MIT license





