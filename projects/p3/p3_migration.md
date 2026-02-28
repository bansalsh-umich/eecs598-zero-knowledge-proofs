# P3 Migration Guide

P3 requires some more substantial edits to your p1 and p2 code. You can either run the
automated script or make the changes by hand.

## Option 1: Run the script

From the directory containing your `p1/`, `p2/`, and `p3/` folders:

```sh
python ./p3_migration .
```

**Note:** This script was written by Claude (with manual review and
modifications). It has been tested against the starter code and staff
solutions, but depending on what changes you made to your own code, it is
possible that the automated patching may not work correctly. For this reason,
the script creates a backup of your `p1/` and `p2/` in `p3_migration_backup/`
before touching anything, and prints a colored diff of every change so you can
verify what it did. If something looks wrong, restore from the backup and apply
the changes by hand using the list below.

## Option 2: Manual changes

### p1

- **`Cargo.toml`** — ensure `serde` with the `derive` feature is in `[dependencies]`:
  ```toml
  serde = { version = "1.0", features = ["derive"] }
  ```

- **`src/lib.rs`** — add `+ FromBytes` as a supertrait of `Field`, and append the following trait + impls at the end of the file:
  ```rust
  pub trait FromBytes: Sized {
      const BYTES_NEEDED: usize;
      fn from_bytes(bytes: &[u8]) -> Self;
  }

  impl FromBytes for u8 {
      const BYTES_NEEDED: usize = 1;
      fn from_bytes(bytes: &[u8]) -> Self { bytes[0] }
  }

  impl<const N: usize, T: FromBytes + std::fmt::Debug> FromBytes for [T; N] {
      const BYTES_NEEDED: usize = N * T::BYTES_NEEDED;
      fn from_bytes(bytes: &[u8]) -> Self {
          assert_eq!(bytes.len(), Self::BYTES_NEEDED);
          bytes.chunks(T::BYTES_NEEDED)
              .map(|chunk| T::from_bytes(chunk))
              .collect::<Vec<T>>().try_into().unwrap()
      }
  }
  ```

- **`src/zq.rs`** — append a `FromBytes` impl for `Zq<Q>`:
  ```rust
  impl<Q: PrimeModulus> crate::FromBytes for Zq<Q> {
      const BYTES_NEEDED: usize = 64;
      fn from_bytes(bytes: &[u8]) -> Self {
          assert!(bytes.len() >= Self::BYTES_NEEDED, "insufficient bytes length");
          let (int, _) = (sfs_bigint::U512::from_le_slice(bytes) % From::from(Q::VALUE)).split();
          Zq::new(int)
      }
  }
  ```

- **`src/curve.rs`**:
  - Add `use serde::{Deserialize, Serialize};` and `use crate::FromBytes;` to imports
  - Add `Default` to the `PrivateZST` derive list
  - Add `Serialize, Deserialize` to the `P256Point` derive list
  - Add `#[serde(skip)]` above the `_priv: PrivateZST` field in the `Point` variant

### p2

- **`Cargo.toml`** — add `serde` with the `derive` feature to `[dependencies]`:
  ```toml
  serde = { version = "1.0", features = ["derive"] }
  ```

- **`src/sparsemat.rs`** — add `use serde::{Deserialize, Serialize};` and add `Serialize, Deserialize` to both the `SparseMatrix` and `SparseVector` derive lists

- **`src/ec.rs`**:
  - Add `use serde::{Serialize, de::DeserializeOwned};` and `iter::Sum` to imports
  - Add `+ Serialize + DeserializeOwned + Sum` to the `EllipticCurve` trait bounds
