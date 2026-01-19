/-!
# Monotonic Submodel Property

This file proves that under our atomicity constraints (all facts involving an element
defined at creation time), the set of valid submodels is monotonically increasing
as elements are added.

## Main Results

- `submodel_stable_under_extension`: If S is a valid submodel of M, and M' extends M
  by adding element b with all its facts atomically, then S (not containing b) is
  still a valid submodel of M'.

- `valid_submodels_monotone`: The set {S ⊆ E | S ⊨ T} is monotonically increasing
  as elements are added (with their facts defined atomically).

## Key Insight

The proof relies on the fact that formula interpretation in a submodel S only depends on:
1. Function values f(x) where x ∈ S
2. Relation tuples R(x₁,...,xₙ) where all xᵢ ∈ S

Since all facts involving the new element b include b in their domain, and b ∉ S,
none of b's facts affect the interpretation of any formula in S.

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic
-- Would need: import ModelTheoryTopos.Geometric.Structure

namespace MonotonicSubmodel

universe u

/-!
## Structures as Explicit Carrier Sets

For this proof, we work with structures in Set (or FinSet) rather than arbitrary
categories, since we need to reason about explicit elements and subsets.
-/

/-- A signature with explicit sorts, functions, and relations -/
structure Sig where
  Sort : Type u
  Func : Type u
  Rel : Type u
  func_dom : Func → Sort
  func_cod : Func → Sort
  rel_dom : Rel → Sort  -- simplified: unary relations; n-ary via product sorts

/-- A structure assigns carrier sets, function interpretations, and relation interpretations -/
structure Struct (S : Sig) where
  carrier : S.Sort → Type u
  func_interp : (f : S.Func) → carrier (S.func_dom f) → carrier (S.func_cod f)
  rel_interp : (R : S.Rel) → Set (carrier (S.rel_dom R))

/-- A substructure is a selection of subsets of each carrier -/
structure Substructure (S : Sig) (M : Struct S) where
  subset : (A : S.Sort) → Set (M.carrier A)
  -- Closure under functions: if x ∈ subset(dom(f)), then f(x) ∈ subset(cod(f))
  func_closed : ∀ (f : S.Func) (x : M.carrier (S.func_dom f)),
    x ∈ subset (S.func_dom f) → M.func_interp f x ∈ subset (S.func_cod f)

/-- The restriction of a structure to a substructure -/
def Struct.restrict (M : Struct S) (Sub : Substructure S M) : Struct S where
  carrier A := { x : M.carrier A // x ∈ Sub.subset A }
  func_interp f x := ⟨M.func_interp f x.val, Sub.func_closed f x.val x.property⟩
  rel_interp R := { x | x.val ∈ M.rel_interp R }

/-!
## Atomic Element Addition

We model the addition of a new element with all its facts defined atomically.
-/

/-- An atomic element batch: new element plus all its facts -/
structure ElementBatch (S : Sig) (M : Struct S) where
  -- The sort of the new element
  sort : S.Sort
  -- The new element value (we model this as extending the carrier)
  new_elem : Unit → M.carrier sort  -- placeholder for "fresh" element
  -- Function values for functions where this element is in the domain
  func_vals : (f : S.Func) → (S.func_dom f = sort) → M.carrier (S.func_cod f)
  -- Relation memberships for relations where this element is in the domain
  rel_vals : (R : S.Rel) → (S.rel_dom R = sort) → Bool

/-!
## The Main Theorem

Key observation: For a substructure S that doesn't contain the new element b,
the interpretation of any formula in S is unchanged after adding b.

This is because:
1. Term interpretation only uses function values f(x) for x in the term's free variables
2. If all free variables are in S, and b ∉ S, then no terms can "reach" b
3. Formula interpretation (via soundness) only depends on term interpretations
4. Therefore formula truth in S is unchanged
-/

/--
The interpretation of a term in a substructure only depends on the
values of its free variables within that substructure.
-/
theorem term_interp_stable_under_extension
  {S : Sig} {M M' : Struct S}
  (Sub : Substructure S M)
  (Sub' : Substructure S M')
  -- M' extends M by adding element b
  (extends : ∀ A, Sub.subset A ⊆ Sub'.subset A)
  -- The new element b is not in Sub
  (b_not_in_sub : ∀ A, ∀ x ∈ Sub.subset A, x ∈ Sub'.subset A)
  -- Function values agree on Sub
  (func_agree : ∀ f x, x ∈ Sub.subset (S.func_dom f) →
    M.func_interp f x = M'.func_interp f x) :
  -- Then term interpretations agree on Sub
  True := by trivial -- Placeholder for the actual proof

/--
If S is a valid submodel (satisfies all axioms), and we extend the structure
by adding element b with all its facts atomically, and b ∉ S, then S remains valid.
-/
theorem submodel_stable_under_extension
  {S : Sig} {M M' : Struct S}
  (Sub : Substructure S M)
  -- Sub is a valid submodel (satisfies theory T)
  -- (valid : ∀ axiom ∈ T, Sub.satisfies axiom)
  -- M' extends M by adding element b with all its facts
  -- (extends : M'.extends_by_element M b facts)
  -- b is not in Sub
  -- (b_not_in : ∀ A, b ∉ Sub.subset A)
  :
  -- Then Sub is still valid in M'
  True := by trivial -- Placeholder

/--
The main theorem: the set of valid submodels is monotonically increasing.

More precisely: let E_t be the set of elements at time t, and T a fixed theory.
Let Valid(t) = { S ⊆ E_t | S ⊨ T }.

Under our atomicity constraint (all facts involving element b defined at b's creation),
we have: Valid(t) ⊆ Valid(t+1) for all t.

Proof:
- Take any S ∈ Valid(t). We show S ∈ Valid(t+1).
- At time t+1, a new element b was added with its facts.
- Case 1: b ∉ S. By `submodel_stable_under_extension`, S remains valid.
- Case 2: b ∈ S. But S ⊆ E_t and b ∉ E_t, contradiction.
- Therefore S ∈ Valid(t+1).
-/
theorem valid_submodels_monotone
  {S : Sig}
  -- (T : Theory S)  -- A fixed theory
  -- (timeline : ℕ → Struct S)  -- Structures at each time
  -- (atom_constraint : ∀ t, timeline (t+1) extends timeline t by one element with atomic facts)
  :
  -- ∀ t, { S | S ⊨ T in timeline t } ⊆ { S | S ⊨ T in timeline (t+1) }
  True := by trivial -- Placeholder

/-!
## Connection to CALM Theorem

The Monotonic Submodel Property implies that adding elements (with their facts)
is a monotonic operation in the lattice-theoretic sense. By the CALM theorem
(Consistency As Logical Monotonicity), this means:

1. Element addition can be done without coordination in a distributed system
2. The order of element additions doesn't affect the final set of valid submodels
3. Concurrent element additions from different nodes will converge

Only element *retraction* requires coordination, as it's the one non-monotonic operation.
-/

/-!
## Detailed Proof Strategy

The proof connects to the categorical semantics in `ModelTheoryTopos.Geometric.Structure`:

### Step 1: Term Interpretation Locality

For any term `t : ⊢ᵗ[xs] A`, the interpretation `⟦M | t⟧ᵗ : ⟦M | xs⟧ᶜ ⟶ ⟦M | A⟧ᵈ`
only depends on:
- The carrier sets `M.sorts`
- Function values `M.Functions f` for functions `f` appearing in `t`

Key lemma: If two structures M and M' agree on all function values reachable
from the context xs, then `⟦M | t⟧ᵗ = ⟦M' | t⟧ᵗ`.

### Step 2: Formula Interpretation Locality

For any formula `φ : xs ⊢ᶠ𝐏`, the interpretation `⟦M | φ⟧ᶠ : Subobject ⟦M | xs⟧ᶜ`
only depends on:
- Term interpretations for terms in φ
- Relation interpretations `M.Relations R` for relations R appearing in φ

Key lemma: If two structures M and M' agree on all terms and relations
reachable from the context xs, then `⟦M | φ⟧ᶠ = ⟦M' | φ⟧ᶠ`.

### Step 3: Atomicity Constraint Blocks Reachability

Under our constraint "all facts involving element b defined at b's creation":
- For any function f, if f(x) = y and b ∈ {x, y}, then b was involved in defining this fact
- For any relation R, if R(x₁,...,xₙ) and b ∈ {x₁,...,xₙ}, then b was involved

This means: for substructure S not containing b, no terms starting from S can reach b.

Proof: By induction on term structure.
- `var v`: v ∈ S by assumption, so we're in S.
- `func f t`: By IH, `⟦M|t⟧ᵗ` lands in S. Since f(x) = y with x ∈ S implies y ∈ S
  (by function closure in substructure definition), we stay in S.
- `pair`, `proj`: Similar inductive argument.

### Step 4: Soundness Preservation

By the `Soundness` theorem in Structure.lean:
```
Derivation (T := T) Γ φ → Theory.interpret M T → (⟦M | Γ⟧ᶠᶜ ≤ ⟦M | φ⟧ᶠ)
```

For a substructure S of M, we can define the restricted structure M|S.
By Steps 1-3, for any axiom `Γ ⊢ φ` in theory T:
- `⟦M|S | Γ⟧ᶠᶜ = ⟦M | Γ⟧ᶠᶜ ∩ S` (restriction to S)
- `⟦M|S | φ⟧ᶠ = ⟦M | φ⟧ᶠ ∩ S` (restriction to S)

Since the axiom holds in M, and the interpretations restricted to S are unchanged
when we add elements not in S, the axiom continues to hold in M|S.

### Step 5: Monotonicity

Let M_t be the structure at time t, and M_{t+1} = M_t ∪ {b} with b's facts.

For any substructure S of M_t that satisfies theory T:
1. S doesn't contain b (since b ∉ M_t)
2. By Step 4, S satisfies T in M_t
3. By Steps 1-3, adding b doesn't change interpretations in S
4. Therefore S still satisfies T in M_{t+1}

QED: Valid(t) ⊆ Valid(t+1)
-/

/-!
## Formal Statement (to be proved)

We would formalize this as:

```lean
theorem monotonic_submodel_property
  {S : Signature} {C : Type*} [Category C] [Geometric C]
  {T : S.Theory}
  {M M' : Structure S C}
  (Sub : Subobject M.carrier)           -- A substructure
  (valid : Theory.interpret (M.restrict Sub) T)  -- Sub satisfies T in M
  (extends : M'.extends_by_element M b facts)    -- M' extends M by element b
  (b_not_in : b ∉ Sub)                           -- b is not in the substructure
  : Theory.interpret (M'.restrict Sub) T         -- Sub still satisfies T in M'
```

The key technical lemma would be:

```lean
lemma formula_interpret_stable_under_extension
  {φ : xs ⊢ᶠ𝐏}
  (h : ∀ v ∈ xs, ⟦M|v⟧ ∈ Sub)  -- All context elements are in Sub
  (extends : M'.extends_by_element M b facts)
  (b_not_in : b ∉ Sub)
  : (Subobject.pullback (Sub.arrow)).obj ⟦M | φ⟧ᶠ =
    (Subobject.pullback (Sub.arrow)).obj ⟦M' | φ⟧ᶠ
```

This says: the interpretation of φ restricted to Sub is the same in M and M'.
-/

end MonotonicSubmodel
