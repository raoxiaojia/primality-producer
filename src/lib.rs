//! Lucas primality certificates and their Lean text, shared by the command-line tool and the
//! WebAssembly page (`wasm`).

pub mod arith;
pub mod driver;
pub mod ecm;
pub mod hints;
pub mod input;
pub mod pm1;
pub mod rho;
pub mod targets;
pub mod task;
pub mod verify;
#[cfg(target_arch = "wasm32")]
pub mod wasm;
