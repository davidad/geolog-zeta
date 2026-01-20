# Geolog

**Geometric Logic REPL** - A language and runtime for formal specifications using geometric logic (coherent logic).

Geolog provides a highly customizable, efficient, concurrent, append-only, persistent, multi-instance memory infrastructure for everything from business process workflow orchestration to formal verification via diagrammatic rewriting.

## Quick Start

```bash
# Build and run
cargo build --release
cargo run

# Or run with an example file
cargo run -- examples/geolog/graph.geolog
```

## Features

- **Theories**: Define sorts (types), functions, relations, and axioms
- **Instances**: Create concrete models of theories
- **Parameterized Theories**: Theories can depend on instances of other theories
- **Nested Instances**: Inline instance definitions within instances
- **Relations**: Binary and n-ary predicates with product domains
- **Axioms**: Horn clauses with existentials and disjunctions in conclusions
- **Chase Algorithm**: Automatic inference of derived facts
- **Interactive REPL**: Explore and modify instances dynamically
- **Version Control**: Commit and track changes to instances

---

## Showcase: Petri Net Reachability

This example demonstrates geolog's power: parameterized theories, the chase algorithm computing transitive closure, and formal specification of Petri net semantics.

### The Theory

```geolog
// Petri net reachability at the place level
theory PlaceReachability {
  P : Sort;  // Places
  T : Sort;  // Transitions

  // Firing relation: which transitions connect which places
  Fires : [trans: T, from: P, to: P] -> Prop;

  // Reachability: transitive closure of firing
  CanReach : [from: P, to: P] -> Prop;

  // Reflexivity
  ax/refl : forall p : P. |- [from: p, to: p] CanReach;

  // Direct firing implies reachability
  ax/fire : forall t : T, x : P, y : P.
    [trans: t, from: x, to: y] Fires |- [from: x, to: y] CanReach;

  // Transitivity
  ax/trans : forall x : P, y : P, z : P.
    [from: x, to: y] CanReach, [from: y, to: z] CanReach
      |- [from: x, to: z] CanReach;
}
```

### Example Instance

```geolog
// Network:  A <--> B --> C
instance SimpleNet : PlaceReachability = {
  A : P;  B : P;  C : P;
  ab : T;  ba : T;  bc : T;

  [trans: ab, from: A, to: B] Fires;
  [trans: ba, from: B, to: A] Fires;
  [trans: bc, from: B, to: C] Fires;
}
```

### REPL Session

```
geolog> :load examples/geolog/petri_reachability.geolog
Defined theory PlaceReachability (2 sorts, 2 relations, 3 axioms)

geolog> :inspect SimpleNet
instance SimpleNet : PlaceReachability = {
  // P (3):
  A : P;  B : P;  C : P;
  // T (3):
  ab : T;  ba : T;  bc : T;
  // Fires (3 tuples):
  [ab, A, B] Fires;
  [ba, B, A] Fires;
  [bc, B, C] Fires;
}

geolog> :chase SimpleNet
✓ Chase completed in 2 iterations

geolog> :inspect SimpleNet
instance SimpleNet : PlaceReachability = {
  ...
  // CanReach (7 tuples) - computed by chase:
  [A, A] CanReach;
  [B, B] CanReach;
  [C, C] CanReach;
  [A, B] CanReach;  // A -> B (direct)
  [B, A] CanReach;  // B -> A (direct)
  [B, C] CanReach;  // B -> C (direct)
  [A, C] CanReach;  // A -> C (transitive: A -> B -> C)
}
```

The chase algorithm automatically computed the full reachability relation, including the transitive closure A → C!

---

## Table of Contents

1. [Basic Concepts](#basic-concepts)
2. [Theory Definitions](#theory-definitions)
3. [Instance Definitions](#instance-definitions)
4. [Relations and Axioms](#relations-and-axioms)
5. [The Chase Algorithm](#the-chase-algorithm)
6. [REPL Commands](#repl-commands)
7. [Complete Examples](#complete-examples)

---

## Basic Concepts

Geolog is based on **geometric logic** (also called coherent logic), a fragment of first-order logic that:
- Allows existential quantification in conclusions
- Allows disjunctions in conclusions
- Is preserved by geometric morphisms (structure-preserving maps)

A **theory** defines:
- **Sorts**: Types of elements
- **Functions**: Maps between sorts
- **Relations**: Predicates on sorts (via `-> Prop`)
- **Axioms**: Logical rules that constrain valid models

An **instance** is a concrete model satisfying a theory.

---

## Theory Definitions

### Simple Theory with Sorts and Functions

```geolog
// Directed Graph: vertices and edges with source/target functions
theory Graph {
  V : Sort;  // Vertices
  E : Sort;  // Edges

  src : E -> V;  // Source of an edge
  tgt : E -> V;  // Target of an edge
}
```

### Theory with Product Domain Functions

```geolog
// Monoid: a set with an associative binary operation
theory Monoid {
  M : Sort;

  // Binary operation: M × M → M
  mul : [x: M, y: M] -> M;

  // Identity element
  id : M -> M;

  // Associativity: (x * y) * z = x * (y * z)
  ax/assoc : forall x : M, y : M, z : M.
    |- [x: [x: x, y: y] mul, y: z] mul = [x: x, y: [x: y, y: z] mul] mul;
}
```

### REPL Session: Defining a Theory Inline

```
geolog> theory Counter {
......    C : Sort;
......    next : C -> C;
......  }
Defined theory Counter (1 sorts, 1 functions)

geolog> :inspect Counter
theory Counter {
  C : Sort;
  next : C -> C;
}
```

---

## Instance Definitions

### Basic Instance

```geolog
// A simple triangle graph: A → B → C → A
instance Triangle : Graph = {
  // Vertices
  A : V;
  B : V;
  C : V;

  // Edges
  ab : E;
  bc : E;
  ca : E;

  // Edge endpoints (function definitions)
  ab src = A;
  ab tgt = B;
  bc src = B;
  bc tgt = C;
  ca src = C;
  ca tgt = A;
}
```

### Instance with Product Domain Functions

```geolog
// Boolean "And" monoid: {T, F} with T as identity
instance BoolAnd : Monoid = {
  T : M;
  F : M;

  // Identity: T is the identity element
  T id = T;
  F id = T;

  // Multiplication table for "and":
  [x: T, y: T] mul = T;
  [x: T, y: F] mul = F;
  [x: F, y: T] mul = F;
  [x: F, y: F] mul = F;
}
```

### REPL Session: Loading and Inspecting

```
geolog> :source examples/geolog/graph.geolog
Loading examples/geolog/graph.geolog...
Defined theory Graph (2 sorts, 2 functions)

geolog> :list
Theories:
  Graph (2 sorts, 2 functions)
Instances:
  Diamond : Graph (8 elements)
  Arrow : Graph (3 elements)
  Loop : Graph (2 elements)
  Triangle : Graph (6 elements)

geolog> :inspect Triangle
instance Triangle : Graph = {
  // V (3):
  A : V;
  B : V;
  C : V;
  // E (3):
  ab : E;
  bc : E;
  ca : E;
  // src:
  ab src = A;
  bc src = B;
  ca src = C;
  // tgt:
  ab tgt = B;
  bc tgt = C;
  ca tgt = A;
}

geolog> :query Triangle V
Elements of V in Triangle:
  A
  B
  C
```

---

## Relations and Axioms

Relations are predicates on sorts, declared with `-> Prop`.

### Unary Relations

```geolog
theory TodoList {
  Item : Sort;

  // Unary relations (predicates on single elements)
  completed : [item: Item] -> Prop;
  high_priority : [item: Item] -> Prop;
  blocked : [item: Item] -> Prop;
}
```

### Binary Relations

```geolog
theory Preorder {
  X : Sort;

  // Binary relation: x ≤ y
  leq : [x: X, y: X] -> Prop;

  // Reflexivity axiom: x ≤ x
  ax/refl : forall x : X.
    |- [x: x, y: x] leq;

  // Transitivity axiom: x ≤ y ∧ y ≤ z → x ≤ z
  ax/trans : forall x : X, y : X, z : X.
    [x: x, y: y] leq, [x: y, y: z] leq |- [x: x, y: z] leq;
}
```

### Asserting Relation Tuples in Instances

```geolog
instance SampleTodos : TodoList = {
  buy_groceries : Item;
  cook_dinner : Item;
  do_laundry : Item;

  // Assert unary relation: buy_groceries is completed
  buy_groceries completed;

  // Assert binary relation: cook_dinner depends on buy_groceries
  [x: cook_dinner, y: buy_groceries] depends_on;
}
```

### REPL Session: Asserting Relations Dynamically

```
geolog> :source examples/geolog/todo_list.geolog
Loading examples/geolog/todo_list.geolog...
Defined theory TodoList (1 sorts, 4 relations)

geolog> :inspect SampleTodos
instance SampleTodos : TodoList = {
  // Item (4):
  buy_groceries : Item;
  cook_dinner : Item;
  do_laundry : Item;
  clean_house : Item;
  // completed (1 tuples):
  [buy_groceries] completed;
  // high_priority (1 tuples):
  [cook_dinner] high_priority;
  // depends_on (1 tuples):
  [cook_dinner, buy_groceries] depends_on;
}

geolog> :assert SampleTodos completed cook_dinner
Asserted completed(cook_dinner) in instance 'SampleTodos'

geolog> :inspect SampleTodos
instance SampleTodos : TodoList = {
  // Item (4):
  buy_groceries : Item;
  cook_dinner : Item;
  do_laundry : Item;
  clean_house : Item;
  // completed (2 tuples):
  [buy_groceries] completed;
  [cook_dinner] completed;
  // high_priority (1 tuples):
  [cook_dinner] high_priority;
  // depends_on (1 tuples):
  [cook_dinner, buy_groceries] depends_on;
}
```

---

## The Chase Algorithm

The **chase algorithm** computes the closure of an instance under the theory's axioms. It derives all facts that logically follow from the base facts and axioms.

### Transitive Closure Example

```geolog
// Graph with reachability (transitive closure)
theory Graph {
  V : Sort;

  // Direct edges
  Edge : [src: V, tgt: V] -> Prop;

  // Reachability (transitive closure of Edge)
  Path : [src: V, tgt: V] -> Prop;

  // Base case: every edge is a path
  ax/base : forall x, y : V.
    [src: x, tgt: y] Edge |- [src: x, tgt: y] Path;

  // Inductive case: paths compose
  ax/trans : forall x, y, z : V.
    [src: x, tgt: y] Path, [src: y, tgt: z] Path |- [src: x, tgt: z] Path;
}

// A linear chain: a -> b -> c -> d
instance Chain : Graph = {
  a : V;
  b : V;
  c : V;
  d : V;

  // Initial edges
  [src: a, tgt: b] Edge;
  [src: b, tgt: c] Edge;
  [src: c, tgt: d] Edge;
}
```

### REPL Session: Running the Chase

```
geolog> :source examples/geolog/transitive_closure.geolog
Loading examples/geolog/transitive_closure.geolog...
Defined theory Graph (1 sorts, 2 relations)

geolog> :inspect Chain
instance Chain : Graph = {
  // V (4):
  a : V;
  b : V;
  c : V;
  d : V;
  // Edge (3 tuples):
  [a, b] Edge;
  [b, c] Edge;
  [c, d] Edge;
}

geolog> :chase Chain
Running chase on instance 'Chain' (theory 'Graph')...
  2 axioms to process
  Compiled axiom 0: axiom_0
  Compiled axiom 1: axiom_1

Executing chase with 2 rules...
✓ Chase completed in 3 iterations (0.15ms)

Structure after chase:
  Elements: 4 total
    V: 4 element(s)
  Relations:
    Edge: 3 tuple(s)
    Path: 6 tuple(s)

geolog> :inspect Chain
instance Chain : Graph = {
  // V (4):
  a : V;
  b : V;
  c : V;
  d : V;
  // Edge (3 tuples):
  [a, b] Edge;
  [b, c] Edge;
  [c, d] Edge;
  // Path (6 tuples):
  [a, b] Path;
  [b, c] Path;
  [c, d] Path;
  [a, c] Path;  // Derived: a->b + b->c
  [b, d] Path;  // Derived: b->c + c->d
  [a, d] Path;  // Derived: a->c + c->d (or a->b + b->d)
}
```

The chase derived:
- **3 base paths** from the Edge → Path axiom
- **2 one-step transitive paths**: (a,c) and (b,d)
- **1 two-step transitive path**: (a,d)

---

## REPL Commands

### General Commands

| Command | Description |
|---------|-------------|
| `:help [topic]` | Show help (topics: syntax, examples) |
| `:quit` | Exit the REPL |
| `:list [target]` | List theories/instances |
| `:inspect <name>` | Show details of a theory or instance |
| `:source <file>` | Load and execute a .geolog file |
| `:clear` | Clear the screen |
| `:reset` | Reset all state |

### Instance Mutation

| Command | Description |
|---------|-------------|
| `:add <inst> <elem> <sort>` | Add element to instance |
| `:assert <inst> <rel> [args]` | Assert relation tuple |
| `:retract <inst> <elem>` | Retract element |

### Query Commands

| Command | Description |
|---------|-------------|
| `:query <inst> <sort>` | List all elements of a sort |
| `:explain <inst> <sort>` | Show query execution plan |
| `:compile <inst> <sort>` | Show RelAlgIR compilation |
| `:chase <inst> [max_iter]` | Run chase algorithm |

### Version Control

| Command | Description |
|---------|-------------|
| `:commit [msg]` | Commit current changes |
| `:history` | Show commit history |

### Solver

| Command | Description |
|---------|-------------|
| `:solve <theory> [budget_ms]` | Find model of theory |
| `:extend <inst> <theory> [budget_ms]` | Extend instance to theory |

### REPL Session: Query Explanation

```
geolog> :source examples/geolog/graph.geolog
Loading examples/geolog/graph.geolog...
Defined theory Graph (2 sorts, 2 functions)

geolog> :explain Triangle V
Query plan for ':query Triangle V':

Scan(sort=0)

Sort: V (index 0)
Instance: Triangle (theory: Graph)

geolog> :explain Triangle E
Query plan for ':query Triangle E':

Scan(sort=1)

Sort: E (index 1)
Instance: Triangle (theory: Graph)
```

---

## Complete Examples

### Example 1: Directed Graphs

**File: `examples/geolog/graph.geolog`**

```geolog
// Directed Graph: vertices and edges with source/target functions
theory Graph {
  V : Sort;  // Vertices
  E : Sort;  // Edges

  src : E -> V;  // Source of an edge
  tgt : E -> V;  // Target of an edge
}

// A simple triangle graph: A → B → C → A
instance Triangle : Graph = {
  A : V;
  B : V;
  C : V;

  ab : E;
  bc : E;
  ca : E;

  ab src = A;
  ab tgt = B;
  bc src = B;
  bc tgt = C;
  ca src = C;
  ca tgt = A;
}

// A self-loop: one vertex with an edge to itself
instance Loop : Graph = {
  v : V;
  e : E;
  e src = v;
  e tgt = v;
}

// Diamond shape with two paths from top to bottom
instance Diamond : Graph = {
  top : V;
  left : V;
  right : V;
  bottom : V;

  top_left : E;
  top_right : E;
  left_bottom : E;
  right_bottom : E;

  top_left src = top;
  top_left tgt = left;
  top_right src = top;
  top_right tgt = right;
  left_bottom src = left;
  left_bottom tgt = bottom;
  right_bottom src = right;
  right_bottom tgt = bottom;
}
```

---

### Example 2: Algebraic Structures (Monoids)

**File: `examples/geolog/monoid.geolog`**

```geolog
// Monoid: a set with an associative binary operation and identity
theory Monoid {
  M : Sort;

  // Binary operation: M × M → M
  mul : [x: M, y: M] -> M;

  // Identity element selector
  id : M -> M;

  // Left identity: id(x) * y = y
  ax/left_id : forall x : M, y : M.
    |- [x: x id, y: y] mul = y;

  // Right identity: x * id(y) = x
  ax/right_id : forall x : M, y : M.
    |- [x: x, y: y id] mul = x;

  // Associativity: (x * y) * z = x * (y * z)
  ax/assoc : forall x : M, y : M, z : M.
    |- [x: [x: x, y: y] mul, y: z] mul = [x: x, y: [x: y, y: z] mul] mul;
}

// Trivial monoid: single element
instance Trivial : Monoid = {
  e : M;
  [x: e, y: e] mul = e;
  e id = e;
}

// Boolean "And" monoid
instance BoolAnd : Monoid = {
  T : M;
  F : M;

  T id = T;
  F id = T;

  [x: T, y: T] mul = T;
  [x: T, y: F] mul = F;
  [x: F, y: T] mul = F;
  [x: F, y: F] mul = F;
}

// Boolean "Or" monoid
instance BoolOr : Monoid = {
  T : M;
  F : M;

  T id = F;
  F id = F;

  [x: T, y: T] mul = T;
  [x: T, y: F] mul = T;
  [x: F, y: T] mul = T;
  [x: F, y: F] mul = F;
}
```

---

### Example 3: Preorders with Chase

**File: `examples/geolog/preorder.geolog`**

```geolog
// Preorder: reflexive and transitive relation
theory Preorder {
  X : Sort;

  // The ordering relation: x ≤ y
  leq : [x: X, y: X] -> Prop;

  // Reflexivity: x ≤ x
  ax/refl : forall x : X.
    |- [x: x, y: x] leq;

  // Transitivity: x ≤ y ∧ y ≤ z → x ≤ z
  ax/trans : forall x : X, y : X, z : X.
    [x: x, y: y] leq, [x: y, y: z] leq |- [x: x, y: z] leq;
}

// Discrete preorder: only reflexive pairs
instance Discrete3 : Preorder = {
  a : X;
  b : X;
  c : X;
}
```

**REPL Session:**

```
geolog> :source examples/geolog/preorder.geolog
Defined theory Preorder (1 sorts, 1 relations)

geolog> :chase Discrete3
Running chase on instance 'Discrete3' (theory 'Preorder')...
✓ Chase completed in 2 iterations

Structure after chase:
  Relations:
    leq: 3 tuple(s)   # (a,a), (b,b), (c,c) - reflexivity only
```

---

### Example 4: Task Management

**File: `examples/geolog/todo_list.geolog`**

```geolog
// TodoList: relational model for task tracking
theory TodoList {
  Item : Sort;

  // Status relations
  completed : [item: Item] -> Prop;
  high_priority : [item: Item] -> Prop;
  blocked : [item: Item] -> Prop;

  // Dependencies
  depends_on : [x: Item, y: Item] -> Prop;

  // Axiom: blocked items depend on incomplete items
  ax/dep_blocked : forall x : Item, y : Item.
    [x: x, y: y] depends_on |- [item: x] blocked \/ [item: y] completed;
}

instance SampleTodos : TodoList = {
  buy_groceries : Item;
  cook_dinner : Item;
  do_laundry : Item;
  clean_house : Item;

  // Mark buy_groceries as completed
  buy_groceries completed;

  // Mark cook_dinner as high priority
  cook_dinner high_priority;

  // cook_dinner depends on buy_groceries
  [x: cook_dinner, y: buy_groceries] depends_on;
}
```

---

### Example 5: Transitive Closure (Chase Demo)

**File: `examples/geolog/transitive_closure.geolog`**

```geolog
// Transitive Closure - demonstrates the chase algorithm
theory Graph {
  V : Sort;

  Edge : [src: V, tgt: V] -> Prop;
  Path : [src: V, tgt: V] -> Prop;

  // Base: edges are paths
  ax/base : forall x, y : V.
    [src: x, tgt: y] Edge |- [src: x, tgt: y] Path;

  // Transitivity: paths compose
  ax/trans : forall x, y, z : V.
    [src: x, tgt: y] Path, [src: y, tgt: z] Path |- [src: x, tgt: z] Path;
}

// Linear chain: a -> b -> c -> d
instance Chain : Graph = {
  a : V;
  b : V;
  c : V;
  d : V;

  [src: a, tgt: b] Edge;
  [src: b, tgt: c] Edge;
  [src: c, tgt: d] Edge;
}

// Diamond: two paths from top to bottom
instance Diamond : Graph = {
  top : V;
  left : V;
  right : V;
  bottom : V;

  [src: top, tgt: left] Edge;
  [src: top, tgt: right] Edge;
  [src: left, tgt: bottom] Edge;
  [src: right, tgt: bottom] Edge;
}

// Cycle: x -> y -> z -> x (chase computes all 9 pairs!)
instance Cycle : Graph = {
  x : V;
  y : V;
  z : V;

  [src: x, tgt: y] Edge;
  [src: y, tgt: z] Edge;
  [src: z, tgt: x] Edge;
}
```

**REPL Session:**

```
geolog> :source examples/geolog/transitive_closure.geolog
Defined theory Graph (1 sorts, 2 relations)

geolog> :chase Chain
✓ Chase completed in 3 iterations
  Edge: 3 tuple(s)
  Path: 6 tuple(s)

geolog> :chase Diamond
✓ Chase completed in 2 iterations
  Edge: 4 tuple(s)
  Path: 5 tuple(s)   # top->left, top->right, left->bottom, right->bottom, top->bottom

geolog> :chase Cycle
✓ Chase completed in 3 iterations
  Edge: 3 tuple(s)
  Path: 9 tuple(s)   # All pairs! (cycle means everything reaches everything)
```

---

### Example 6: Inline Definitions

You can define theories and instances directly in the REPL:

```
geolog> theory Counter {
......    C : Sort;
......    next : C -> C;
......  }
Defined theory Counter (1 sorts, 1 functions)

geolog> instance Mod3 : Counter = {
......    zero : C;
......    one : C;
......    two : C;
......    zero next = one;
......    one next = two;
......    two next = zero;
......  }
Defined instance Mod3 : Counter (3 elements)

geolog> :inspect Mod3
instance Mod3 : Counter = {
  // C (3):
  zero : C;
  one : C;
  two : C;
  // next:
  zero next = one;
  one next = two;
  two next = zero;
}
```

---

## Syntax Reference

### Sorts
```
identifier : Sort;
```

### Functions
```
// Unary function
name : Domain -> Codomain;

// Binary function (product domain)
name : [field1: Sort1, field2: Sort2] -> Codomain;
```

### Relations
```
// Unary relation
name : [field: Sort] -> Prop;

// Binary relation
name : [x: Sort1, y: Sort2] -> Prop;
```

### Axioms
```
// No premises (fact)
name : forall vars. |- conclusion;

// With premises
name : forall vars. premise1, premise2 |- conclusion;

// With disjunction in conclusion
name : forall vars. premise |- conclusion1 \/ conclusion2;
```

### Instance Elements
```
elem_name : Sort;
```

### Function Values
```
// Unary
elem func = value;

// Product domain
[field1: val1, field2: val2] func = value;
```

### Relation Assertions
```
// Unary relation
elem relation;

// Binary relation
[field1: val1, field2: val2] relation;
```

---

## Architecture

Geolog is built on several key components:

- **Parser**: Converts `.geolog` source to AST
- **Elaborator**: Type-checks and converts AST to core representations
- **Structure**: In-memory model representation with carriers and functions
- **Chase Engine**: Fixpoint computation for derived relations
- **Query Engine**: Relational algebra for querying instances
- **Store**: Persistent, append-only storage with version control

---

## License

MIT License - see LICENSE file for details.

---

## Contributing

Contributions welcome! See CLAUDE.md for development guidelines and the `loose_thoughts/` directory for design discussions.
