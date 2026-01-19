# Geolog Architecture

Geolog is a language for geometric logic with semantics in topoi. This document describes the module structure and data flow.

## Module Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              USER INTERFACE                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│  repl.rs          Interactive REPL with commands (:help, :inspect, etc.)   │
│  bin/geolog.rs    CLI entry point                                           │
└───────────────────────────────┬─────────────────────────────────────────────┘
                                │
┌───────────────────────────────▼─────────────────────────────────────────────┐
│                           PARSING / SURFACE LAYER                            │
├─────────────────────────────────────────────────────────────────────────────┤
│  lexer.rs         Tokenization (chumsky-based)                              │
│  parser.rs        Token stream → AST (chumsky-based)                        │
│  ast.rs           Surface syntax AST types                                  │
│  pretty.rs        Core → geolog source (inverse of parsing)                 │
│  error.rs         Error formatting with source spans                        │
└───────────────────────────────┬─────────────────────────────────────────────┘
                                │
┌───────────────────────────────▼─────────────────────────────────────────────┐
│                            ELABORATION LAYER                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│  elaborate/                                                                 │
│    ├── mod.rs     Re-exports                                                │
│    ├── env.rs     Elaboration environment (theory registry)                 │
│    ├── theory.rs  AST theory → Core theory elaboration                      │
│    ├── instance.rs AST instance → Core structure elaboration                │
│    └── error.rs   Elaboration error types                                   │
│                                                                             │
│  Transforms surface AST into typed core representation                      │
└───────────────────────────────┬─────────────────────────────────────────────┘
                                │
┌───────────────────────────────▼─────────────────────────────────────────────┐
│                              CORE LAYER                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│  core.rs          Core IR: Signature, Term, Formula, Structure              │
│                   - Signature: sorts + functions + relations                │
│                   - Term: Var | App | Record | Project                      │
│                   - Formula: True | False | Eq | Rel | Conj | Disj | Exists │
│                   - Structure: carriers + function maps + relation storage  │
│                                                                             │
│  id.rs            Identity system (Luid = global, Slid = structure-local)   │
│  universe.rs      Global element registry (Luid allocation)                 │
│  naming.rs        Bidirectional name ↔ Luid mapping                         │
└───────────────────────────────┬─────────────────────────────────────────────┘
                                │
┌───────────────────────────────▼─────────────────────────────────────────────┐
│                            STORAGE LAYER                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│  workspace.rs     Session management (theories + instances + naming)        │
│  patch.rs         Patch-based structure modifications                       │
│  version.rs       Git-like version control for structures                   │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                         SOLVING LAYER (frontier)                             │
├─────────────────────────────────────────────────────────────────────────────┤
│  solver/                                                                    │
│    ├── mod.rs     Re-exports and overview                                   │
│    ├── types.rs   SearchNode, Obligation, NodeStatus, etc.                  │
│    ├── tree.rs    Explicit search tree for model finding                    │
│    └── tactics.rs Automated search tactics (Check, Enumerate, Propagate)   │
│                                                                             │
│  tensor/                                                                    │
│    ├── mod.rs     Re-exports                                                │
│    ├── expr.rs    Lazy tensor expression trees                              │
│    ├── sparse.rs  Sparse tensor storage (RoaringTreemap)                    │
│    ├── builder.rs Expression builders (conjunction, disjunction, exists)   │
│    ├── compile.rs Formula → TensorExpr compilation                          │
│    └── check.rs   Axiom checking via tensor evaluation                      │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                         META LAYER (self-description)                        │
├─────────────────────────────────────────────────────────────────────────────┤
│  meta.rs          Rust codegen for GeologMeta theory                        │
│  theories/GeologMeta.geolog   Homoiconic theory representation              │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Data Flow

### Parsing / Pretty-Printing Flow
```
Source text → lexer.rs → Token stream → parser.rs → ast::File
                                                         ↓
core::Structure ← elaborate ←──────────────────────── ast::*
       ↓
pretty.rs → Source text   (roundtrip!)
```

### Elaboration Flow
```
ast::TheoryDecl  →  elaborate/theory.rs  →  core::Theory (Signature + Axioms)
ast::InstanceDecl →  elaborate/instance.rs → core::Structure
```

### REPL Flow
```
User input → ReplState::process_line → MetaCommand | GeologInput
                                              ↓
                    GeologInput → parse → elaborate → workspace.add_*
```

## Key Types

### Identity System

```rust
Luid  // "Local Universe ID" - globally unique across all structures
Slid  // "Structure-Local ID" - index within a single structure

// A Structure maps Slid → Luid for global identity
structure.get_luid(slid) -> Luid
```

### Core Representation

```rust
// Signatures define the vocabulary
Signature {
    sorts: Vec<String>,           // Sort names by SortId
    functions: Vec<FunctionSymbol>,  // f : A → B
    relations: Vec<RelationSymbol>,  // R : A → Prop
}

// Structures interpret signatures
Structure {
    carriers: Vec<RoaringBitmap>,  // Elements per sort (as Slid)
    functions: Vec<HashMap<...>>,  // Function value maps
    relations: Vec<VecRelation>,   // Relation extents
    local_to_global: Vec<Luid>,    // Slid → Luid
}
```

### Axioms (Sequents)

```rust
Sequent {
    context: Context,      // Universally quantified variables
    premise: Formula,      // Antecedent (conjunction of atomics)
    conclusion: Formula,   // Consequent (positive geometric formula)
}
```

## Design Principles

1. **Postfix application**: `x f` not `f(x)` — matches categorical composition
2. **Child pointers**: Parent → Child, not Child → Parent (no products in domains)
3. **Upward binding**: Variables point to their binders (scoping is explicit)
4. **Sparse storage**: Relations use RoaringBitmap for efficient membership
5. **Patch-based updates**: Structures evolve via patches, enabling versioning
6. **Explicit search tree**: Solver maintains tree in memory, not call stack

## Testing Strategy

- **proptest**: Property-based tests for core operations (naming, patches, structure)
- **unit tests**: Specific behaviors in `tests/unit_*.rs`
- **integration tests**: Example .geolog files in `tests/examples_integration.rs`
- **REPL testing**: Interactive exploration via `cargo run`

## Future Directions

See `bd ready` for current work items. Key frontiers:

- **Solver completion** (`geolog-xj2`): Full geometric logic model finding
- **Congruence closure** (`geolog-fjy`): Equation handling in solver
- **Leapfrog Triejoin** (`geolog-bpd`): Efficient multi-way joins
- **Product instance elaboration** (`geolog-ulh`): `[x: a, y: b] mul = c` syntax
