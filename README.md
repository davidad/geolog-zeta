# Geolog

> This README was synthesized automatically by Claude Opus 4.5.
> As was this entire project, really.

**Geometric Logic REPL** - A language and runtime for formal specifications using geometric logic.

Geolog aims to provide a highly customizable, efficient, concurrent, append-only, persistent memory and query infrastructure for everything from business process workflow orchestration to formal verification via diagrammatic rewriting.

## Quick Start

```bash
~/dev/geolog$ cargo install --path .
   Compiling geolog v0.1.0 (/home/dev/geolog)
    Finished release [optimized] target(s) in 12.34s
  Installing ~/.cargo/bin/geolog
   Installed package `geolog v0.1.0` (executable `geolog`)

~/dev/geolog$ geolog -d foo
geolog v0.1.0 - Geometric Logic REPL
Type :help for help, :quit to exit

Workspace: foo
geolog> theory Graph {
  V : Sort;
  E : Sort;
  src : E -> V;
  tgt : E -> V;
  reachable : [from: V, to: V] -> Prop;

  ax/edge : forall e : E. |- [from: e src, to: e tgt] reachable;
  ax/trans : forall x : V, y : V, z : V.
    [from: x, to: y] reachable, [from: y, to: z] reachable
    |- [from: x, to: z] reachable;
}
Defined theory Graph (2 sorts, 2 functions, 1 relations)

geolog> instance G : Graph = chase {
  a : V;
  b : V;
  c : V;
  e1 : E; e1 src = a; e1 tgt = b;
  e2 : E; e2 src = b; e2 tgt = c;
}
Defined instance G : Graph (5 elements) [chase: 3 iterations]

geolog> :commit "graph with reachability"
Committed: "graph with reachability" (commit #17)

geolog> :quit
Goodbye!

~/dev/geolog$ geolog -d foo
geolog v0.1.0 - Geometric Logic REPL
Type :help for help, :quit to exit

Workspace: foo
geolog> :list
Theories:
  Graph (2 sorts, 2 functions, 1 relations)
Instances:
  G : Graph (5 elements)

geolog> :inspect G
instance G : Graph = {
  // V (3):
  a : V;
  b : V;
  c : V;
  // E (2):
  e1 : E;
  e2 : E;
  // src:
  e1 src = a;
  e2 src = b;
  // tgt:
  e1 tgt = b;
  e2 tgt = c;
  // reachable (3 tuples):
  [from: a, to: b] reachable;
  [from: b, to: c] reachable;
  [from: a, to: c] reachable;
}

geolog> :query G reachable a
Tuples matching reachable(a, _) in G:
  [from: a, to: b]
  [from: a, to: c]
```

## Features

- **Theories**: Define sorts (types), functions, relations, and axioms
- **Instances**: Create concrete models of theories
- **Parameterized Theories**: Theories can depend on instances of other theories
- **Nested Instances**: Inline instance definitions within instances
- **Relations**: Binary and n-ary predicates with product domains
- **Axioms**: Geometric sequents, automatically checked with tensor algebra
- **Chase Algorithm**: Automatic inference of derived facts
- **Interactive REPL**: Explore and modify instances dynamically
- **Version Control**: Commit and track changes to instances

---

## Showcase: Petri Net Reachability as Dependent Types

This showcase demonstrates geolog's core capabilities through a non-trivial domain:
encoding Petri net reachability as dependent types. A solution to a reachability
problem is NOT a yes/no boolean but a **constructive witness**: a diagrammatic proof
that tokens can flow from initial to target markings via a sequence of transition firings.

**Key concepts demonstrated:**
- Parameterized theories (`Marking` depends on `PetriNet` instance)
- Nested instance types (`ReachabilityProblem` contains `Marking` instances)
- Sort-parameterized theories (`Iso` takes two sorts as parameters)
- Cross-instance references (solution's trace elements reference problem's tokens)

> **Note**: This showcase is tested by `cargo test test_petri_net_showcase` and
> matches `examples/geolog/petri_net_showcase.geolog` exactly.

### The Type-Theoretic Encoding

```geolog
// ============================================================
// THEORY: PetriNet - Places, transitions, and arcs
// ============================================================

theory PetriNet {
  P : Sort;      // Places
  T : Sort;      // Transitions
  in : Sort;     // Input arcs (place -> transition)
  out : Sort;    // Output arcs (transition -> place)

  in/src : in -> P;    // Input arc source place
  in/tgt : in -> T;    // Input arc target transition
  out/src : out -> T;  // Output arc source transition
  out/tgt : out -> P;  // Output arc target place
}

// ============================================================
// THEORY: Marking (parameterized by N : PetriNet)
// A marking assigns tokens to places
// ============================================================

theory (N : PetriNet instance) Marking {
  token : Sort;
  token/of : token -> N/P;
}

// ============================================================
// THEORY: ReachabilityProblem (parameterized by N : PetriNet)
// Initial and target markings as nested instances
// ============================================================

theory (N : PetriNet instance) ReachabilityProblem {
  initial_marking : N Marking instance;
  target_marking : N Marking instance;
}

// ============================================================
// THEORY: Trace (parameterized by N : PetriNet)
// A trace records transition firings and token flow via wires
// ============================================================

theory (N : PetriNet instance) Trace {
  F : Sort;                         // Firings
  F/of : F -> N/T;                  // Which transition each firing corresponds to

  // Wires connect output arcs of firings to input arcs of other firings
  W : Sort;
  W/src_firing : W -> F;
  W/src_arc : W -> N/out;
  W/tgt_firing : W -> F;
  W/tgt_arc : W -> N/in;

  // Wire coherence axioms (source/target arcs must match firing transitions)
  ax/wire_src_coherent : forall w : W. |- w W/src_arc N/out/src = w W/src_firing F/of;
  ax/wire_tgt_coherent : forall w : W. |- w W/tgt_arc N/in/tgt = w W/tgt_firing F/of;
  ax/wire_place_coherent : forall w : W. |- w W/src_arc N/out/tgt = w W/tgt_arc N/in/src;

  // Terminals connect initial/target markings to firings
  input_terminal : Sort;
  output_terminal : Sort;
  input_terminal/of : input_terminal -> N/P;
  output_terminal/of : output_terminal -> N/P;
  input_terminal/tgt_firing : input_terminal -> F;
  input_terminal/tgt_arc : input_terminal -> N/in;
  output_terminal/src_firing : output_terminal -> F;
  output_terminal/src_arc : output_terminal -> N/out;

  // Terminal coherence axioms
  ax/input_terminal_coherent : forall i : input_terminal.
    |- i input_terminal/tgt_arc N/in/tgt = i input_terminal/tgt_firing F/of;
  ax/output_terminal_coherent : forall o : output_terminal.
    |- o output_terminal/src_arc N/out/src = o output_terminal/src_firing F/of;

  // Terminal place coherence
  ax/input_terminal_place : forall i : input_terminal.
    |- i input_terminal/of = i input_terminal/tgt_arc N/in/src;
  ax/output_terminal_place : forall o : output_terminal.
    |- o output_terminal/of = o output_terminal/src_arc N/out/tgt;

  // COMPLETENESS: Every arc of every firing must be accounted for.

  // Input completeness: every input arc must be fed by a wire or input terminal
  ax/input_complete : forall f : F, arc : N/in.
    arc N/in/tgt = f F/of |-
    (exists w : W. w W/tgt_firing = f, w W/tgt_arc = arc) \/
    (exists i : input_terminal. i input_terminal/tgt_firing = f, i input_terminal/tgt_arc = arc);

  // Output completeness: every output arc must be captured by a wire or output terminal
  ax/output_complete : forall f : F, arc : N/out.
    arc N/out/src = f F/of |-
    (exists w : W. w W/src_firing = f, w W/src_arc = arc) \/
    (exists o : output_terminal. o output_terminal/src_firing = f, o output_terminal/src_arc = arc);
}

// ============================================================
// THEORY: Iso (parameterized by two sorts)
// Isomorphism (bijection) between two sorts
// ============================================================

theory (X : Sort) (Y : Sort) Iso {
  fwd : X -> Y;
  bwd : Y -> X;

  // Roundtrip axioms ensure this is a true bijection
  fb : forall x : X. |- x fwd bwd = x;
  bf : forall y : Y. |- y bwd fwd = y;
}

// ============================================================
// THEORY: Solution (parameterized by N and RP)
// A constructive witness that target is reachable from initial
// ============================================================

theory (N : PetriNet instance) (RP : N ReachabilityProblem instance) Solution {
  trace : N Trace instance;

  // Bijection: input terminals <-> initial marking tokens
  initial_iso : (trace/input_terminal) (RP/initial_marking/token) Iso instance;

  // Bijection: output terminals <-> target marking tokens
  target_iso : (trace/output_terminal) (RP/target_marking/token) Iso instance;
}
```

### Problem 0: Can we reach B from A with one token?

```geolog
// ============================================================
// The Petri Net:
//       +---[ba]----+
//       v           |
//      (A) --[ab]->(B) --+
//       |                |
//       +----[abc]-------+--> (C)
// ============================================================

instance ExampleNet : PetriNet = {
  A : P; B : P; C : P;
  ab : T; ba : T; abc : T;

  // A -> B (via ab)
  ab_in : in;  ab_in in/src = A; ab_in in/tgt = ab;
  ab_out : out; ab_out out/src = ab; ab_out out/tgt = B;

  // B -> A (via ba)
  ba_in : in;  ba_in in/src = B; ba_in in/tgt = ba;
  ba_out : out; ba_out out/src = ba; ba_out out/tgt = A;

  // A + B -> C (via abc) - note: two input arcs!
  abc_in1 : in; abc_in1 in/src = A; abc_in1 in/tgt = abc;
  abc_in2 : in; abc_in2 in/src = B; abc_in2 in/tgt = abc;
  abc_out : out; abc_out out/src = abc; abc_out out/tgt = C;
}

// Initial: 1 token in A, Target: 1 token in B
instance problem0 : ExampleNet ReachabilityProblem = {
  initial_marking = {
    tok : token;
    tok token/of = ExampleNet/A;
  };
  target_marking = {
    tok : token;
    tok token/of = ExampleNet/B;
  };
}

// ============================================================
// SOLUTION 0: Yes! Fire transition 'ab' once.
// ============================================================

instance solution0 : ExampleNet problem0 Solution = {
  trace = {
    f1 : F;
    f1 F/of = ExampleNet/ab;

    // Input terminal feeds A-token into f1's ab_in arc
    it : input_terminal;
    it input_terminal/of = ExampleNet/A;
    it input_terminal/tgt_firing = f1;
    it input_terminal/tgt_arc = ExampleNet/ab_in;

    // Output terminal captures f1's B-token via ab_out arc
    ot : output_terminal;
    ot output_terminal/of = ExampleNet/B;
    ot output_terminal/src_firing = f1;
    ot output_terminal/src_arc = ExampleNet/ab_out;
  };

  initial_iso = {
    trace/it fwd = problem0/initial_marking/tok;
    problem0/initial_marking/tok bwd = trace/it;
  };

  target_iso = {
    trace/ot fwd = problem0/target_marking/tok;
    problem0/target_marking/tok bwd = trace/ot;
  };
}
```

### Problem 2: Can we reach C from two A-tokens?

This is a more interesting case: the only path to C is via `abc`, which requires
tokens in BOTH A and B simultaneously. Starting with 2 tokens in A, we must
first move one to B, then fire `abc`.

```geolog
// Initial: 2 tokens in A, Target: 1 token in C
instance problem2 : ExampleNet ReachabilityProblem = {
  initial_marking = {
    t1 : token; t1 token/of = ExampleNet/A;
    t2 : token; t2 token/of = ExampleNet/A;
  };
  target_marking = {
    t : token;
    t token/of = ExampleNet/C;
  };
}

// ============================================================
// SOLUTION 2: Fire 'ab' then 'abc'.
//
// Token flow diagram:
//   [it1]--A-->[f1: ab]--B--wire-->[f2: abc]--C-->[ot]
//   [it2]--A-----------------^
//
// Step 1: Fire 'ab' to move one token A -> B
// Step 2: Fire 'abc' consuming one A-token and one B-token
// ============================================================

instance solution2 : ExampleNet problem2 Solution = {
  trace = {
    // Two firings
    f1 : F; f1 F/of = ExampleNet/ab;   // First: A -> B
    f2 : F; f2 F/of = ExampleNet/abc;  // Second: A + B -> C

    // Wire connecting f1's B-output to f2's B-input
    w1 : W;
    w1 W/src_firing = f1;
    w1 W/src_arc = ExampleNet/ab_out;
    w1 W/tgt_firing = f2;
    w1 W/tgt_arc = ExampleNet/abc_in2;

    // Input terminal 1: feeds first A-token into f1
    it1 : input_terminal;
    it1 input_terminal/of = ExampleNet/A;
    it1 input_terminal/tgt_firing = f1;
    it1 input_terminal/tgt_arc = ExampleNet/ab_in;

    // Input terminal 2: feeds second A-token into f2
    it2 : input_terminal;
    it2 input_terminal/of = ExampleNet/A;
    it2 input_terminal/tgt_firing = f2;
    it2 input_terminal/tgt_arc = ExampleNet/abc_in1;

    // Output terminal: captures f2's C-token output
    ot : output_terminal;
    ot output_terminal/of = ExampleNet/C;
    ot output_terminal/src_firing = f2;
    ot output_terminal/src_arc = ExampleNet/abc_out;
  };

  // Bijection: 2 input terminals <-> 2 initial tokens
  initial_iso = {
    trace/it1 fwd = problem2/initial_marking/t1;
    trace/it2 fwd = problem2/initial_marking/t2;
    problem2/initial_marking/t1 bwd = trace/it1;
    problem2/initial_marking/t2 bwd = trace/it2;
  };

  // Bijection: 1 output terminal <-> 1 target token
  target_iso = {
    trace/ot fwd = problem2/target_marking/t;
    problem2/target_marking/t bwd = trace/ot;
  };
}
```

Each `Solution` instance is a **constructive diagrammatic proof**:
- The trace contains firing(s) of specific transitions
- Input terminals witness that initial tokens feed into firings
- Output terminals witness that firings produce target tokens
- The isomorphisms prove the token counts match exactly

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

Geolog is based on **geometric logic**, a fragment of first-order logic that:
- Allows existential quantification in conclusions
- Allows disjunctions in conclusions
- Is preserved by geometric morphisms (structure-preserving maps)

A **theory** defines:
- **Sorts**: Types of elements
- **Function symbols**: Function-typed variables with domain and codomain derived from sorts
- **Relation symbols**: Predicate-typed variables with domain derived from sorts, and codomain `-> Prop`
- **Axioms**: Geometric sequents (first universal quantifiers, then an implication between two propositions which are then purely positive)

An **instance** is a concrete finite model, which means it assigns to each sort a finite set, to each function a finite function, and to each relation a Boolean-valued tensor, such that all axioms evaluate to true.

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

  // Unary relations use simple arrow syntax
  completed : Item -> Prop;
  high_priority : Item -> Prop;
  blocked : Item -> Prop;
}
```

### Binary Relations

```geolog
theory Preorder {
  X : Sort;

  // Binary relation: x ≤ y (field names document the relation)
  leq : [lo: X, hi: X] -> Prop;

  // Reflexivity axiom: x ≤ x
  ax/refl : forall x : X.
    |- [lo: x, hi: x] leq;

  // Transitivity axiom: x ≤ y ∧ y ≤ z → x ≤ z
  ax/trans : forall x : X, y : X, z : X.
    [lo: x, hi: y] leq, [lo: y, hi: z] leq |- [lo: x, hi: z] leq;
}
```

### Asserting Relation Tuples in Instances

```geolog
instance SampleTodos : TodoList = {
  buy_groceries : Item;
  cook_dinner : Item;
  do_laundry : Item;
  clean_house : Item;

  // Assert unary relation: buy_groceries is completed
  buy_groceries completed;

  // Assert unary relation: cook_dinner is high priority
  cook_dinner high_priority;

  // Binary relation using mixed positional/named syntax:
  // First positional arg maps to 'item' field, named arg for 'on'
  [cook_dinner, on: buy_groceries] depends;
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
  // depends (1 tuples):
  [cook_dinner, buy_groceries] depends;
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
  // depends (1 tuples):
  [cook_dinner, buy_groceries] depends;
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
// Using `= chase { ... }` to automatically apply axioms during elaboration.
instance Chain : Graph = chase {
  a : V;
  b : V;
  c : V;
  d : V;

  // Initial edges (chase derives Path tuples)
  [src: a, tgt: b] Edge;
  [src: b, tgt: c] Edge;
  [src: c, tgt: d] Edge;
}
```

### REPL Session: Running the Chase

When using `= chase { ... }` syntax, the chase runs automatically during elaboration:

```
geolog> :source examples/geolog/transitive_closure.geolog
Loading examples/geolog/transitive_closure.geolog...
Defined theory Graph (1 sorts, 2 relations)
Defined instance Chain : Graph (4 elements) [chase: 6 Path tuples derived]

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

You can also run chase manually with `:chase` on non-chase instances:

```
geolog> :chase MyInstance
Running chase on instance 'MyInstance' (theory 'Graph')...
✓ Chase completed in 3 iterations (0.15ms)
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
// Uses `chase` to automatically derive reflexive pairs from ax/refl.
instance Discrete3 : Preorder = chase {
  a : X;
  b : X;
  c : X;
}

// A total order on 3 elements: bot ≤ mid ≤ top
instance Chain3 : Preorder = chase {
  bot : X;
  mid : X;
  top : X;

  [x: bot, y: mid] leq;
  [x: mid, y: top] leq;
  // Chase derives: (bot,bot), (mid,mid), (top,top) + (bot,top)
}
```

**REPL Session:**

```
geolog> :source examples/geolog/preorder.geolog
Defined theory Preorder (1 sorts, 1 relations)
Defined instance Discrete3 : Preorder (3 elements) [chase: 3 leq tuples derived]
Defined instance Chain3 : Preorder (3 elements) [chase: 6 leq tuples derived]

geolog> :inspect Discrete3
  leq: 3 tuple(s)   // (a,a), (b,b), (c,c) - reflexivity only

geolog> :inspect Chain3
  leq: 6 tuple(s)   // reflexive pairs + given + transitive (bot,top)
```

---

### Example 4: Task Management

**File: `examples/geolog/todo_list.geolog`**

```geolog
// TodoList: relational model for task tracking
theory TodoList {
  Item : Sort;

  // Status relations (unary, simple arrow syntax)
  completed : Item -> Prop;
  high_priority : Item -> Prop;
  blocked : Item -> Prop;

  // Dependencies (binary, with named fields)
  depends : [item: Item, on: Item] -> Prop;

  // Axiom: blocked items depend on incomplete items
  ax/dep_blocked : forall x : Item, y : Item.
    [item: x, on: y] depends |- x blocked \/ y completed;
}

instance SampleTodos : TodoList = {
  buy_groceries : Item;
  cook_dinner : Item;
  do_laundry : Item;
  clean_house : Item;

  // Unary relations: simple syntax
  buy_groceries completed;
  cook_dinner high_priority;

  // Binary relation: mixed positional/named syntax
  // First positional arg -> 'item', named arg for 'on'
  [cook_dinner, on: buy_groceries] depends;
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

// Linear chain: a -> b -> c -> d (chase runs automatically)
instance Chain : Graph = chase {
  a : V;
  b : V;
  c : V;
  d : V;

  [src: a, tgt: b] Edge;
  [src: b, tgt: c] Edge;
  [src: c, tgt: d] Edge;
}

// Diamond: two paths from top to bottom
instance Diamond : Graph = chase {
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
instance Cycle : Graph = chase {
  x : V;
  y : V;
  z : V;

  [src: x, tgt: y] Edge;
  [src: y, tgt: z] Edge;
  [src: z, tgt: x] Edge;
}
```

**REPL Session** (chase runs during `:source`):

```
geolog> :source examples/geolog/transitive_closure.geolog
Defined theory Graph (1 sorts, 2 relations)
Defined instance Chain : Graph (4 elements) [chase: 6 Path tuples]
Defined instance Diamond : Graph (4 elements) [chase: 5 Path tuples]
Defined instance Cycle : Graph (3 elements) [chase: 9 Path tuples]
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

> TODO: greatly expand this section

Geolog is built with several key components:

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
