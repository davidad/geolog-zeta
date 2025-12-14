# Geolog Roadmap

## Current: Elaboration
Turn surface syntax AST into typed internal representation (closer to Owen's Lean formalization).

## Backlog

### Testing Infrastructure
- **Deep AST equality** — recursive comparison for roundtrip tests
- **Property-based testing** — generate random ASTs, print, re-parse, compare (QuickCheck/proptest)

### Developer Experience
- **Ariadne error messages** — pretty error reporting with source spans (crate already in Cargo.toml)

### Future Features
- (to be discovered during elaboration)
