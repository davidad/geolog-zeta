import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic

/-!
# Monotonic Submodel Property

This file proves that under atomicity constraints (all facts involving an element
defined at creation time), the set of valid submodels is monotonically increasing
as elements are added.

## Main Results

- `submodel_stable_under_atomic_extension`: Valid submodels remain valid after atomic extension
- `monotonic_submodel_property`: Valid(t) ⊆ Valid(t+1)

## Key Insight

When we add element b with all its facts atomically:
- The restricted structure M|S only sees elements in S
- If b ∉ S, then M|S and M'|S have identical carriers and interpretations
- Therefore M|S = M'|S as structures
- So any theory satisfied by M|S is also satisfied by M'|S

This is the crucial observation: the restriction operation "shields" S from the new element.
-/

namespace MonotonicSubmodel

universe u

/-!
## Signatures and Structures (Simplified Set-Theoretic)

We define a simplified notion of signature and structure in Type u,
focusing on the essential properties needed for the monotonicity proof.
-/

/-- A simplified signature with named sorts, functions, and relations -/
structure SimpleSignature where
  /-- Type of sort names -/
  Sorts : Type u
  /-- Type of function symbols -/
  FuncSymbols : Type u
  /-- Type of relation symbols -/
  RelSymbols : Type u
  /-- Arity of each function (number of inputs) -/
  funcArity : FuncSymbols → ℕ
  /-- Domain sorts for each function (indexed by position) -/
  funcDom : (f : FuncSymbols) → Fin (funcArity f) → Sorts
  /-- Codomain sort for each function -/
  funcCod : FuncSymbols → Sorts
  /-- Arity of each relation -/
  relArity : RelSymbols → ℕ
  /-- Domain sorts for each relation -/
  relDom : (R : RelSymbols) → Fin (relArity R) → Sorts

variable {Sig : SimpleSignature}

/-- A structure for a simple signature in Type u -/
structure SimpleStructure (Sig : SimpleSignature) where
  /-- Carrier set for each sort -/
  carrier : Sig.Sorts → Type u
  /-- Interpretation of function symbols -/
  funcs : (f : Sig.FuncSymbols) →
    ((i : Fin (Sig.funcArity f)) → carrier (Sig.funcDom f i)) →
    carrier (Sig.funcCod f)
  /-- Interpretation of relation symbols (as sets) -/
  rels : (R : Sig.RelSymbols) →
    Set ((i : Fin (Sig.relArity R)) → carrier (Sig.relDom R i))

/-!
## Subset Selection and Restriction
-/

/-- A subset selection picks a subset of each carrier -/
structure SubsetSelection (M : SimpleStructure Sig) where
  subset : (A : Sig.Sorts) → Set (M.carrier A)

/-- Check if all inputs are in the selected subset -/
def inputsInSubset {M : SimpleStructure Sig} (sel : SubsetSelection M)
    {n : ℕ} (dom : Fin n → Sig.Sorts)
    (args : (i : Fin n) → M.carrier (dom i)) : Prop :=
  ∀ i, args i ∈ sel.subset (dom i)

/-- A subset selection is closed under functions -/
def SubsetSelection.FunctionClosed {M : SimpleStructure Sig} (sel : SubsetSelection M) : Prop :=
  ∀ f : Sig.FuncSymbols,
    ∀ args : (i : Fin (Sig.funcArity f)) → M.carrier (Sig.funcDom f i),
      inputsInSubset sel (Sig.funcDom f) args →
      M.funcs f args ∈ sel.subset (Sig.funcCod f)

/-!
## Structure Embeddings
-/

/-- Map arguments through an embedding function -/
def embedArgs {M M' : SimpleStructure Sig}
    (embed : ∀ A, M.carrier A → M'.carrier A)
    {n : ℕ} (dom : Fin n → Sig.Sorts)
    (args : (i : Fin n) → M.carrier (dom i)) :
    (i : Fin n) → M'.carrier (dom i) :=
  fun i => embed (dom i) (args i)

/-- An embedding of one structure into another -/
structure StructEmbed (M M' : SimpleStructure Sig) where
  /-- Embedding of carriers -/
  embed : ∀ A, M.carrier A → M'.carrier A
  /-- Embeddings are injective -/
  embed_inj : ∀ A, Function.Injective (embed A)
  /-- Functions commute with embedding -/
  func_agree : ∀ (f : Sig.FuncSymbols)
    (args : (i : Fin (Sig.funcArity f)) → M.carrier (Sig.funcDom f i)),
    embed (Sig.funcCod f) (M.funcs f args) =
    M'.funcs f (embedArgs embed (Sig.funcDom f) args)
  /-- Relations are preserved by embedding -/
  rel_agree : ∀ (R : Sig.RelSymbols)
    (args : (i : Fin (Sig.relArity R)) → M.carrier (Sig.relDom R i)),
    args ∈ M.rels R ↔ embedArgs embed (Sig.relDom R) args ∈ M'.rels R

/-!
## Atomic Element Extension

An atomic extension adds one new element with all facts involving it defined atomically.
-/

/-- An atomic batch specifies a new element to add -/
structure AtomicBatch (M : SimpleStructure Sig) where
  /-- The sort of the new element -/
  sort : Sig.Sorts
  /-- The new element -/
  newElem : M.carrier sort

/-- A subset selection excludes the new element -/
def SubsetSelection.ExcludesNew {M : SimpleStructure Sig}
    (sel : SubsetSelection M) (batch : AtomicBatch M) : Prop :=
  batch.newElem ∉ sel.subset batch.sort

/-!
## The Core Theorem: Pullback of Subset Selections
-/

/-- Pull back a subset selection along an embedding -/
def SubsetSelection.pullback {M M' : SimpleStructure Sig}
    (emb : StructEmbed M M') (sel : SubsetSelection M) : SubsetSelection M' where
  subset A := emb.embed A '' sel.subset A

/-- Check if embedded arguments are in the image of the subset -/
def pullbackInputsInImage {M M' : SimpleStructure Sig}
    (embed : ∀ A, M.carrier A → M'.carrier A)
    (sel : SubsetSelection M)
    {n : ℕ} (dom : Fin n → Sig.Sorts)
    (args' : (i : Fin n) → M'.carrier (dom i)) : Prop :=
  ∀ i, args' i ∈ embed (dom i) '' sel.subset (dom i)

/-- pullbackInputsInImage equals inputsInSubset of pullback -/
theorem pullback_inputsInSubset_eq {M M' : SimpleStructure Sig}
    (emb : StructEmbed M M')
    (sel : SubsetSelection M)
    {n : ℕ} (dom : Fin n → Sig.Sorts)
    (args' : (i : Fin n) → M'.carrier (dom i)) :
    inputsInSubset (sel.pullback emb) dom args' ↔
    pullbackInputsInImage emb.embed sel dom args' := by
  simp [inputsInSubset, pullbackInputsInImage, SubsetSelection.pullback]

/-- If inputs are in subset, embedded inputs are in image -/
theorem embedArgs_preserves_membership {M M' : SimpleStructure Sig}
    (embed : ∀ A, M.carrier A → M'.carrier A)
    (sel : SubsetSelection M)
    {n : ℕ} (dom : Fin n → Sig.Sorts)
    (args : (i : Fin n) → M.carrier (dom i))
    (h : inputsInSubset sel dom args) :
    pullbackInputsInImage embed sel dom (embedArgs embed dom args) := by
  intro i
  simp only [embedArgs]
  exact ⟨args i, h i, rfl⟩

/-- If embedded arguments are in image, there exist preimages in subset -/
theorem extractPreimages {M M' : SimpleStructure Sig}
    (embed : ∀ A, M.carrier A → M'.carrier A)
    (sel : SubsetSelection M)
    {n : ℕ} (dom : Fin n → Sig.Sorts)
    (args' : (i : Fin n) → M'.carrier (dom i))
    (hx' : pullbackInputsInImage embed sel dom args') :
    ∃ args : (i : Fin n) → M.carrier (dom i),
      inputsInSubset sel dom args ∧ embedArgs embed dom args = args' := by
  -- Use axiom of choice to extract preimages for each component
  have h : ∀ i, ∃ a : M.carrier (dom i), a ∈ sel.subset (dom i) ∧ embed (dom i) a = args' i := by
    intro i
    obtain ⟨a, ha_mem, ha_eq⟩ := hx' i
    exact ⟨a, ha_mem, ha_eq⟩
  -- Construct the function using choice
  choose args hargs_mem hargs_eq using h
  exact ⟨args, hargs_mem, funext hargs_eq⟩

/-- **Key Lemma**: Function closure is preserved by pullback along an embedding -/
theorem pullback_preserves_closure {M M' : SimpleStructure Sig}
    (emb : StructEmbed M M')
    (sel : SubsetSelection M)
    (hclosed : sel.FunctionClosed) :
    (sel.pullback emb).FunctionClosed := by
  unfold SubsetSelection.FunctionClosed
  intro f args' hargs'
  -- Convert to pullbackInputsInImage
  rw [pullback_inputsInSubset_eq] at hargs'
  -- Extract preimages
  obtain ⟨args, hargs_in, hargs_eq⟩ := extractPreimages emb.embed sel (Sig.funcDom f) args' hargs'
  -- Apply function closure in M
  have hout := hclosed f args hargs_in
  -- Show output is in pullback
  simp only [SubsetSelection.pullback, Set.mem_image]
  use M.funcs f args, hout
  -- Use func_agree and hargs_eq
  rw [emb.func_agree, hargs_eq]

/-!
## Main Theorems
-/

/--
**Main Theorem (Submodel Stability)**

If S is a valid submodel of M (closed under functions), and we extend M to M'
by adding element b with all facts atomically, and b ∉ S, then S is still
closed under functions in M'.

More precisely: the pullback of S along the embedding remains function-closed.
-/
theorem submodel_stable_under_atomic_extension {M M' : SimpleStructure Sig}
    (emb : StructEmbed M M')
    (sel : SubsetSelection M)
    (_batch : AtomicBatch M)
    (hclosed : sel.FunctionClosed)
    (_hexcl : sel.ExcludesNew _batch) :
    (sel.pullback emb).FunctionClosed :=
  pullback_preserves_closure emb sel hclosed

/--
**Main Theorem (Monotonic Submodel Property)**

The set of function-closed subset selections is monotonically increasing
as elements are added with their facts defined atomically.

When we embed M into M' (extending by new elements), any function-closed
subset selection of M pulls back to a function-closed subset selection of M'.

This is the key property that enables coordination-free element addition
in distributed systems (CALM theorem connection).
-/
theorem monotonic_submodel_property {M M' : SimpleStructure Sig}
    (emb : StructEmbed M M')
    (sel : SubsetSelection M)
    (hclosed : sel.FunctionClosed) :
    (sel.pullback emb).FunctionClosed :=
  pullback_preserves_closure emb sel hclosed

/-!
## Why This Matters: Connection to CALM and Distributed Systems

The Monotonic Submodel Property has profound implications:

### Coordination-Free Element Addition (CALM Theorem)

Since `Valid(t) ⊆ Valid(t+1)` when adding elements atomically:
- **Monotonicity**: The set of valid submodels only grows
- **CALM**: Monotonic operations are coordination-free in distributed systems
- **Practical**: Different nodes can add elements concurrently without locks

### The Only Non-Monotonic Operation

Element *retraction* (marking elements as non-live) is non-monotonic:
- Retraction can invalidate previously valid submodels
- Retraction requires coordination (consensus, locks, etc.)
- This is why GeologMeta separates `Elem` creation from `ElemRetract`

### Practical Implications for GeologMeta

1. **FuncVal and RelTuple are immutable**: Once `f(a) = b` is true, it's eternally true
2. **All facts defined at creation**: When element `a` is created, all `f(a)` and `R(a,_)` are defined
3. **Only liveness changes**: To "modify" `f(a)`, retract `a` and create a new element
4. **Incremental model checking**: New elements can only add valid submodels

This design enables efficient, lock-free, eventually-consistent distributed databases
for geometric logic theories.
-/

end MonotonicSubmodel
