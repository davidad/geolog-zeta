//! Fuzz the geolog parser
//!
//! This target exercises the lexer and parser to find edge cases
//! and potential panics in the parsing code.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Try to interpret the data as UTF-8
    if let Ok(input) = std::str::from_utf8(data) {
        // The parser should never panic, even on malformed input
        // It should return an error instead
        let _ = geolog::parse(input);
    }
});
