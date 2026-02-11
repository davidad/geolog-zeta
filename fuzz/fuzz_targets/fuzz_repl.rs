//! Fuzz the geolog REPL execution
//!
//! This target exercises the full REPL pipeline: parsing, elaboration,
//! and instance creation. It should never panic on any input.

#![no_main]

use libfuzzer_sys::fuzz_target;
use geolog::repl::ReplState;

fuzz_target!(|data: &[u8]| {
    // Try to interpret the data as UTF-8
    if let Ok(input) = std::str::from_utf8(data) {
        // Create a fresh REPL state for each fuzz input
        // (in-memory, no persistence)
        let mut state = ReplState::new();

        // The REPL should never panic on any input
        // It should return a Result<_, String> error instead
        let _ = state.execute_geolog(input);
    }
});
