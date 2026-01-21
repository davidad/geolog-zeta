# Geolog Surface Syntax Reference

This document describes the surface syntax of Geolog. For examples, see `examples/geolog/`.

## Lexical Elements

### Identifiers
```
identifier := [a-zA-Z_][a-zA-Z0-9_]*
```

### Paths
Paths use `/` as a separator (not `.`), which allows `.` for field projection:
```
path := identifier ('/' identifier)*
```
Examples: `P`, `in/src`, `ax/refl`

### Keywords
```
namespace  theory  instance  query
Sort  Prop  forall  exists
```

### Operators and Punctuation
```
:  ->  =  |-  \/  .  ,  ;
{  }  [  ]  (  )
```

## Declarations

A Geolog file consists of declarations:

```
file := declaration*
declaration := namespace | theory | instance | query
```

### Namespace
```
namespace identifier;
```
Currently a no-op; reserved for future module system.

### Theory

```ebnf
theory := 'theory' params? identifier '{' theory_item* '}'
params := param_group+
param_group := '(' param (',' param)* ')'
param := identifier ':' type_expr

theory_item := sort_decl | function_decl | axiom_decl | field_decl
```

#### Sort Declaration
```
identifier ':' 'Sort' ';'
```
Example: `P : Sort;`

#### Function Declaration
```
path ':' type_expr '->' type_expr ';'
```
Examples:
```
src : E -> V;                    // Unary function
mul : [x: M, y: M] -> M;         // Binary function (product domain)
```

#### Relation Declaration
Relations are functions to `Prop`:
```
path ':' type_expr '->' 'Prop' ';'
```
Example:
```
leq : [x: X, y: X] -> Prop;      // Binary relation
```

#### Axiom Declaration
```
path ':' 'forall' quantified_vars '.' premises '|-' conclusion ';'

quantified_vars := var_group (',' var_group)*
var_group := identifier (',' identifier)* ':' type_expr
premises := formula (',' formula)*    // May be empty
```

Examples:
```
// No premises (Horn clause with empty body)
ax/refl : forall x : X. |- [x: x, y: x] leq;

// With premises
ax/trans : forall x : X, y : X, z : X.
  [x: x, y: y] leq, [x: y, y: z] leq |- [x: x, y: z] leq;
```

### Instance

```ebnf
instance := 'instance' identifier ':' type_expr '=' instance_body
instance_body := '{' instance_item* '}' | 'chase' '{' instance_item* '}'

instance_item := element_decl | equation | nested_instance
```

Using `= chase { ... }` runs the chase algorithm during elaboration, automatically deriving facts from axioms.

#### Element Declaration
```
identifier ':' type_expr ';'
```
Example: `A : V;` — declares element `A` of sort `V`

#### Equation
```
term '=' term ';'
```
Example: `ab src = A;` — asserts that applying `src` to `ab` yields `A`

#### Nested Instance (syntax parsed but not fully elaborated)
```
identifier '=' '{' instance_item* '}' ';'
```

## Type Expressions

```ebnf
type_expr := 'Sort' | 'Prop' | path | record_type | app_type | arrow_type | instance_type

record_type := '[' (field (',' field)*)? ']'
field := identifier ':' type_expr    // Named field
       | type_expr                   // Positional: gets name "0", "1", etc.

app_type := type_expr type_expr          // Juxtaposition
arrow_type := type_expr '->' type_expr
instance_type := type_expr 'instance'
```

Examples:
```
Sort                    // The universe of sorts
Prop                    // Propositions
V                       // A named sort
[x: M, y: M]           // Product type with named fields
[M, M]                 // Product type with positional fields ("0", "1")
[M, on: M]             // Mixed: first positional, second named
M -> M                  // Function type
PetriNet instance      // Instance of a theory
N PetriNet instance    // Parameterized: N is a PetriNet instance
```

## Terms

```ebnf
term := path | record | paren_term | application | projection

record := '[' (entry (',' entry)*)? ']'
entry := identifier ':' term         // Named entry
       | term                        // Positional: gets name "0", "1", etc.

paren_term := '(' term ')'
application := term term           // Postfix! 'x f' means 'f(x)'
projection := term '.' identifier  // Record projection
```

**Important**: Geolog uses **postfix** function application.

| Geolog | Traditional |
|--------|-------------|
| `x f` | `f(x)` |
| `[x: a, y: b] mul` | `mul(a, b)` |
| `x f g` | `g(f(x))` |

This matches categorical composition: morphisms compose left-to-right.

Examples:
```
A                       // Variable/element reference
ab src                  // Apply src to ab
[x: a, y: b] mul       // Apply mul to record (named fields)
[a, b] mul             // Apply mul to record (positional)
[a, on: b] rel         // Mixed: positional first, named second
x f g                   // Composition: g(f(x))
r .field               // Project field from record r
```

**Note on positional fields**: Positional fields are assigned names "0", "1", etc.
When matching against a relation defined with named fields (e.g., `rel : [x: M, y: M] -> Prop`),
positional fields are matched by position: "0" matches the first field, "1" the second, etc.
This allows mixing positional and named syntax: `[a, y: b] rel` is equivalent to `[x: a, y: b] rel`.

## Formulas

```ebnf
formula := atomic | exists | disjunction | paren_formula

atomic := equality | relation_app
equality := term '=' term
relation_app := term identifier     // 'x R' means R(x)

exists := 'exists' quantified_vars '.' formula
disjunction := formula ('\/' formula)+
paren_formula := '(' formula ')'
```

**Conjunction** is implicit: premises in axioms separated by `,` form a conjunction.

Examples:
```
x = y                           // Equality
[x: a, y: b] leq               // Relation application
exists z : X. [x: x, y: z] leq // Existential
phi \/ psi                     // Disjunction
```

## Comments

Line comments start with `//`:
```
// This is a comment
P : Sort;  // Inline comment
```

## Complete Example

```geolog
// Directed graph theory
theory Graph {
  V : Sort;
  E : Sort;
  src : E -> V;
  tgt : E -> V;
}

// A triangle: A → B → C → A
instance Triangle : Graph = {
  A : V;
  B : V;
  C : V;

  ab : E;
  ab src = A;
  ab tgt = B;

  bc : E;
  bc src = B;
  bc tgt = C;

  ca : E;
  ca src = C;
  ca tgt = A;
}
```

## Grammar Summary (EBNF)

```ebnf
file := declaration*

declaration := 'namespace' ident ';'
             | 'theory' params? ident '{' theory_item* '}'
             | 'instance' ident ':' type '=' '{' instance_item* '}'
             | 'query' ident ':' type '=' formula

params := ('(' param (',' param)* ')')+
param := ident ':' type

theory_item := ident ':' 'Sort' ';'
             | path ':' type '->' type ';'
             | path ':' 'forall' qvars '.' formulas '|-' formula ';'

qvars := (ident (',' ident)* ':' type) (',' ...)*
formulas := formula (',' formula)*

instance_item := ident ':' type ';'
               | term '=' term ';'
               | ident '=' '{' instance_item* '}' ';'

type := 'Sort' | 'Prop' | path | '[' fields ']' | type type | type '->' type | type 'instance'
fields := (ident ':' type) (',' ...)*

term := path | '[' entries ']' | '(' term ')' | term term | term '.' ident
entries := (ident ':' term) (',' ...)*

formula := term '=' term | term ident | 'exists' qvars '.' formula | formula '\/' formula | '(' formula ')'

path := ident ('/' ident)*
ident := [a-zA-Z_][a-zA-Z0-9_]*
```

## Example Files

The `examples/geolog/` directory contains working examples:

| File | Description |
|------|-------------|
| `graph.geolog` | Simple directed graph theory with vertices and edges |
| `preorder.geolog` | Preorder (reflexive, transitive relation) with discrete/chain instances |
| `transitive_closure.geolog` | **Demonstrates chase algorithm** - computes reachability |
| `monoid.geolog` | Algebraic monoid theory with associativity axiom |
| `petri_net.geolog` | Petri net formalization with places, transitions, marking |
| `petri_net_showcase.geolog` | **Full showcase** - parameterized theories, nested instances, cross-references |
| `todo_list.geolog` | Task management example with dependencies |
| `solver_demo.geolog` | Solver demonstration with reachability queries |
| `relalg_simple.geolog` | Simple RelAlgIR query plan examples |

### Running Examples

```bash
# Start REPL with an example
cargo run -- examples/geolog/graph.geolog

# Or load interactively
cargo run
:source examples/geolog/transitive_closure.geolog
:inspect Chain
:chase Chain   # Computes transitive closure!
```
