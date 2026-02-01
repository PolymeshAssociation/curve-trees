#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

// This code is ported from [Monero's codebase](https://github.com/monero-oxide/monero-oxide/blob/fcmp%2B%2B/crypto/fcmps/ec-gadgets/src/dlog.rs)
 
extern crate core;

pub mod dlog;
pub mod utils;
pub mod error;
