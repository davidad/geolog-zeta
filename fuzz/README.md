# Fuzzing geolog

This directory contains fuzz targets for finding bugs and edge cases in geolog.

## Requirements

Fuzzing requires the nightly Rust compiler due to sanitizer support:

```bash
rustup install nightly
rustup default nightly  # or use +nightly flag
```

## Available Targets

- **fuzz_parser**: Exercises the lexer and parser with arbitrary UTF-8 input
- **fuzz_repl**: Exercises the full REPL execution pipeline

## Running Fuzzers

```bash
# List all fuzz targets
cargo fuzz list

# Run the parser fuzzer
cargo +nightly fuzz run fuzz_parser

# Run the REPL fuzzer
cargo +nightly fuzz run fuzz_repl

# Run with a time limit (e.g., 60 seconds)
cargo +nightly fuzz run fuzz_parser -- -max_total_time=60

# Run with a corpus directory
cargo +nightly fuzz run fuzz_parser corpus/fuzz_parser
```

## Corpus

Interesting inputs found during fuzzing are automatically saved to `corpus/<target_name>/`.
These can be used to reproduce issues:

```bash
# Reproduce a crash
cargo +nightly fuzz run fuzz_parser corpus/fuzz_parser/<crash_file>
```

## Minimizing Crashes

```bash
cargo +nightly fuzz tmin fuzz_parser <crash_file>
```

## Coverage

Generate coverage reports:

```bash
cargo +nightly fuzz coverage fuzz_parser
```
