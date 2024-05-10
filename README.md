# free-list

[![Crates.io](https://img.shields.io/crates/v/free-list)](https://crates.io/crates/free-list)
[![docs.rs](https://img.shields.io/docsrs/free-list)](https://docs.rs/free-list)
[![CI](https://github.com/mkroening/free-list/actions/workflows/ci.yml/badge.svg)](https://github.com/mkroening/free-list/actions/workflows/ci.yml)

This crate provides the [`FreeList`] type to allocate pages/frames of virtual/physical memory:

```rust
use free_list::{FreeList, PageLayout};

let mut free_list = FreeList::<16>::new();

unsafe {
    free_list.deallocate((0x1000..0x5000).try_into().unwrap()).unwrap();
}
assert_eq!(free_list.free_space(), 0x4000);

let layout = PageLayout::from_size(0x4000).unwrap();
assert_eq!(free_list.allocate(layout).unwrap(), (0x1000..0x5000).try_into().unwrap());
```

For API documentation, see the [docs].

[`FreeList`]: https://docs.rs/free-list/latest/free_list/struct.FreeList.html
[docs]: https://docs.rs/free-list

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
