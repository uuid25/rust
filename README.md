# Uuid25: 25-digit case-insensitive UUID encoding

[![Crates.io](https://img.shields.io/crates/v/uuid25)](https://crates.io/crates/uuid25)
[![License](https://img.shields.io/crates/l/uuid25)](https://github.com/uuid25/rust/blob/main/LICENSE)

Uuid25 is an alternative UUID representation that shortens a UUID string to just
25 digits using the case-insensitive Base36 encoding. This library provides
functionality to convert from the conventional UUID formats to Uuid25 and vice
versa.

```rust
use uuid25::Uuid25;

// convert from/to string
let a = Uuid25::parse("8da942a4-1fbe-4ca6-852c-95c473229c7d")?;
assert_eq!(a, "8dx554y5rzerz1syhqsvsdw8t");
assert_eq!(a.to_hyphenated(), "8da942a4-1fbe-4ca6-852c-95c473229c7d");

// convert from/to 128-bit byte array
let b = Uuid25::from([0xff; 16]);
assert_eq!(b, "f5lxx1zz5pnorynqglhzmsp33");
assert_eq!(b.to_bytes(), [0xff; 16]);

// convert from/to other popular textual representations
let c = [
    Uuid25::parse("e7a1d63b711744238988afcf12161878")?,
    Uuid25::parse("e7a1d63b-7117-4423-8988-afcf12161878")?,
    Uuid25::parse("{e7a1d63b-7117-4423-8988-afcf12161878}")?,
    Uuid25::parse("urn:uuid:e7a1d63b-7117-4423-8988-afcf12161878")?,
];
assert_eq!(c, ["dpoadk8izg9y4tte7vy1xt94o"; 4]);

let d = Uuid25::parse("dpoadk8izg9y4tte7vy1xt94o")?;
assert_eq!(d.to_hex(), "e7a1d63b711744238988afcf12161878");
assert_eq!(d.to_hyphenated(), "e7a1d63b-7117-4423-8988-afcf12161878");
assert_eq!(d.to_braced(), "{e7a1d63b-7117-4423-8988-afcf12161878}");
assert_eq!(d.to_urn(), "urn:uuid:e7a1d63b-7117-4423-8988-afcf12161878");

// convert from/to uuid crate's Uuid value (enabled by uuid feature)
let uuid_crate = uuid::uuid!("f38a6b1f-576f-4c22-8d4a-5f72613483f6");
let e = Uuid25::from(uuid_crate);
assert_eq!(e, "ef1zh7jc64vprqez41vbwe9km");
assert_eq!(uuid::Uuid::from(e), uuid_crate);

// create value in const context
const K: Uuid25 = Uuid25::parse_unwrap("ae5f2947-0784-48de-af26-690bc03b1f22");
assert_eq!(K, "abmwj0hrnat6qdyswurn714bm");

// generate new UUID in Uuid25 format (enabled by gen feature)
println!("{}", uuid25::gen_v4()); // e.g., "99wfqtl0z0yevxzpl4hv2dm5p"
```

## Integration with other crates

This crate implements conversion traits from/into UUID types of other popular
crates. To enable such conversion traits, turn on the corresponding crate
features. For example, to enable conversion from/into `uuid::Uuid`, put the
following entries in `Cargo.toml`:

```toml
[dependencies]
uuid   = { version = "<version>", features = ["v4"] }
uuid25 = { version = "<version>", features = ["uuid"] }
```

And then:

```rust
use uuid25::Uuid25;

let x: Uuid25 = uuid::Uuid::new_v4().into();
println!("{}", x); // e.g., "6n7pvwv8r54xycmuby0pp1q8a"

let y: uuid::Uuid = x.into();
println!("{}", y); // e.g., "703d4a3e-5f1a-473e-90dd-fe20c883780a"
```

## Crate features

Default features:

- `std` integrates this crate with `std` and enables integration with
  `std::string::String` and `std::error::Error`. Note that this crate does
  not rely a lot on `std` and most of the functionality of this crate is still
  available under `no_std` environments.

Optional features:

- `serde` enables serialization/deserialization of `Uuid25` values through
  `serde`
- `uuid` enables conversion traits from/into `uuid::Uuid`
- `bson` enables conversion traits from/into `bson::Uuid`
- `uuid7` enables conversion traits from/into `uuid7::Uuid`
- `gen` enables `gen_v4()` and `gen_v7()` functions that generate UUIDs in the
  Uuid25 format (backed by `uuid7` crate; depends on `std` and `uuid7` features)

## Command-line interface

This crate includes a simple filter program that converts the conventional UUID
strings into Uuid25 and vice versa. Install the command by:

```sh
cargo install --example uuid25-filter uuid25
```

Usage:

```sh
$ cat uuid-strings.txt
1xl7tld67nekvdlrp0pkvsut5
20a6bddafff4faa14e8fc0eb75a169f9
20a6bdda-fff4-faa1-4e8f-c0eb75a169f9
{20a6bdda-fff4-faa1-4e8f-c0eb75a169f9}
urn:uuid:20a6bdda-fff4-faa1-4e8f-c0eb75a169f9
$
$ cat uuid-strings.txt | uuid25-filter
1xl7tld67nekvdlrp0pkvsut5
1xl7tld67nekvdlrp0pkvsut5
1xl7tld67nekvdlrp0pkvsut5
1xl7tld67nekvdlrp0pkvsut5
1xl7tld67nekvdlrp0pkvsut5
$
$ cat uuid-strings.txt | uuid25-filter --to hyphenated
20a6bdda-fff4-faa1-4e8f-c0eb75a169f9
20a6bdda-fff4-faa1-4e8f-c0eb75a169f9
20a6bdda-fff4-faa1-4e8f-c0eb75a169f9
20a6bdda-fff4-faa1-4e8f-c0eb75a169f9
20a6bdda-fff4-faa1-4e8f-c0eb75a169f9
```

## License

Licensed under the Apache License, Version 2.0.

## See also

- [docs.rs/uuid25](https://docs.rs/uuid25)
