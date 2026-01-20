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
│  store/                                                                     │
│    ├── mod.rs           Store struct: unified GeologMeta persistence        │
│    ├── schema.rs        Schema ID caches (sort_ids, func_ids, etc.)         │
│    ├── append.rs        Append-only element/function/relation creation      │
│    ├── theory.rs        Theory → Store integration                          │
│    ├── instance.rs      Instance → Store integration                        │
│    ├── commit.rs        Git-like commit/version control                     │
│    └── bootstrap_queries.rs  Hardcoded query patterns (being replaced)      │
│                                                                             │
│  workspace.rs     Legacy session management (deprecated, use Store)         │
│  patch.rs         Patch-based structure modifications                       │
│  version.rs       Git-like version control for structures                   │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                            QUERY LAYER                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│  query/                                                                     │
│    ├── mod.rs         Re-exports and overview                               │
│    ├── compile.rs     Query → QueryOp plan compilation                      │
│    ├── backend.rs     Naive QueryOp executor (reference impl)               │
│    ├── optimize.rs    Algebraic law rewriting (filter fusion, etc.)         │
│    ├── pattern.rs     Legacy Pattern API (deprecated)                       │
│    └── store_queries.rs  Store-level compiled query methods                 │
│                                                                             │
│  Relational query engine for GeologMeta and instance queries.               │
│  Query API: Query::scan(sort).filter_eq(func, col, val).compile()           │
│  Optimizer applies RelAlgIR laws: Filter(p, Filter(q, x)) → Filter(p∧q, x)  │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                         SOLVING LAYER (frontier)                             │
├─────────────────────────────────────────────────────────────────────────────┤
│  solver/                                                                    │
│    ├── mod.rs     Unified model enumeration API + re-exports                │
│    │              - enumerate_models(): core unified function               │
│    │              - solve(): find models from scratch                       │
│    │              - query(): extend existing models                         │
│    ├── types.rs   SearchNode, Obligation, NodeStatus, CongruenceClosure     │
│    ├── tree.rs    Explicit search tree with from_base() for extensions      │
│    └── tactics.rs Automated search tactics:                                 │
│                   - CheckTactic: axiom checking, obligation reporting       │
│                   - ForwardChainingTactic: Datalog-style forward chaining   │
│                   - PropagateEquationsTactic: congruence closure propagation│
│                   - AutoTactic: composite fixpoint solver                   │
│                                                                             │
│  REPL commands: `:solve <theory>`, `:extend <instance> <theory>`            │
│  See examples/geolog/solver_demo.geolog for annotated examples.             │
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

- **Query engine** (`geolog-7tt`, `geolog-32x`): Chase algorithm and RelAlgIR compiler
- **Nested instance elaboration** (`geolog-1d4`): Inline instance definitions
- **Monotonic Submodel proofs** (`geolog-rgg`): Lean4 formalization
- **Disjunction variable alignment** (`geolog-69b`): Extend tensor builder for heterogeneous disjuncts

## Recent Milestones

- **Unified model enumeration API** (`2026-01-19`): Consolidated `solve()`, `extend()`, and `query()`
  into single `enumerate_models()` function. REPL commands `:solve` and `:extend` now share underlying implementation.

- **Tensor compiler improvements** (`2026-01-20`):
  - Function application equalities: `f(x) = y`, `y = f(x)`, `f(x) = g(y)` now compile correctly
  - Empty-domain existential fix: `∃x. φ` on empty domain correctly returns false
  - Closed `geolog-dxr` (tensor compilation panics on function terms)

- **Bootstrap query migration** (`2026-01-20`): All 6 bootstrap_queries functions now delegate
  to compiled query engine (`store_queries.rs`). Net reduction of ~144 lines of handcoded iteration.

- **Proptest coverage** (`2026-01-20`): Added 6 solver proptests covering trivial theories,
  inconsistent theories, existential theories, and Horn clause propagation.

- **Geometric logic solver complete** (`geolog-xj2`): Forward chaining, equation propagation,
  existential body processing, derivation search for False. Interactive via `:solve`.
