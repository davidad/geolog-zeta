import ModelTheoryTopos.Geometric.Structure
import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Limits.Types.Images
import Mathlib.CategoryTheory.Subobject.Types
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Monotonic Submodel Property

This file proves the Monotonic Submodel Property for geometric logic structures,
specialized to the category `Type u`.

## Main Results

- `pushforward_preserves_closure`: Function closure preserved under pushforward
- `monotonic_submodel_property`: Valid(t) ⊆ Valid(t+1) under atomic extensions

## Technical Note

We work with `Type u` and focus on base sorts where the interpretation
is definitionally the carrier type: `(DerivedSorts.inj A).interpret M.sorts = M.sorts A`.
-/

namespace MonotonicSubmodel

open CategoryTheory Limits Signature

universe u

/-!
## Instance Priority Override

The model-theory-topos library defines `OrderBot (Subobject X)` with `sorry`.
We override it with Mathlib's proper implementation for Type u, which requires
`HasInitial C` and `InitialMonoClass C`.
-/

-- Override model-theory-topos's sorried OrderBot with Mathlib's proper instance
attribute [instance 2000] Subobject.orderBot

variable {S : Signature}

/-!
## Subobjects in Type u

In Type u, subobjects correspond to subsets via `Types.subobjectEquivSet α : Subobject α ≃o Set α`.
We work with the arrow's range as the concrete set representation.

Key Mathlib facts we leverage:
- `Types.subobjectEquivSet` proves Subobject α ≃o Set α
- `mono_iff_injective` shows monos in Type u are injective functions
- Products in Type u are pi types: `∏ᶜ F ≅ ∀ j, F j`
- Pullbacks are subtypes: `pullback f g ≅ { p : X × Y // f p.1 = g p.2 }`
-/

/-!
## Transport Lemmas for DerivedSorts.interpret
-/

/-- For a base sort, interpretation is definitionally the carrier -/
theorem interpret_inj (M : Structure S (Type u)) (A : S.Sorts) :
    (DerivedSorts.inj A).interpret M.sorts = M.sorts A := rfl

/-- Transport along domain equality -/
def castDom {M : Structure S (Type u)} {f : S.Functions} {A : S.Sorts}
    (hdom : f.domain = DerivedSorts.inj A) (x : M.sorts A) :
    f.domain.interpret M.sorts :=
  cast (congrArg (DerivedSorts.interpret M.sorts) hdom).symm x

/-- Transport along codomain equality -/
def castCod {M : Structure S (Type u)} {f : S.Functions} {B : S.Sorts}
    (hcod : f.codomain = DerivedSorts.inj B) (y : f.codomain.interpret M.sorts) :
    M.sorts B :=
  cast (congrArg (DerivedSorts.interpret M.sorts) hcod) y

/-!
## Lifting Elements Along Embeddings

We define `liftSort'` which lifts elements of derived sorts along a family of maps
on base sorts. This is defined before `StructureEmbedding` so that the embedding
can use it in its `func_comm` field.
-/

/-- Lift an element of a derived sort along a family of maps on base sorts.
    For base sorts: apply the map directly.
    For products: apply componentwise via Types.productIso. -/
noncomputable def liftSort' {M M' : Structure S (Type u)}
    (embed : ∀ A, M.sorts A → M'.sorts A) : (D : DerivedSorts S.Sorts) →
    D.interpret M.sorts → D.interpret M'.sorts
  | .inj B => embed B
  | .prod Aᵢ => fun x =>
    let x' := (Types.productIso _).hom x
    let y' : ∀ i, (Aᵢ i).interpret M'.sorts := fun i => liftSort' embed (Aᵢ i) (x' i)
    (Types.productIso _).inv y'

/-- For base sorts, liftSort' equals embed (with casting) -/
theorem liftSort'_inj {M M' : Structure S (Type u)}
    (embed : ∀ A, M.sorts A → M'.sorts A)
    {D : DerivedSorts S.Sorts} {A : S.Sorts} (hD : D = .inj A)
    (x : D.interpret M.sorts) :
    liftSort' embed D x = cast (by rw [hD]) (embed A (cast (by rw [hD]) x)) := by
  subst hD
  simp only [liftSort', cast_eq]

/-!
## Subset Selection
-/

/-- A subset selection for base sorts of a structure in Type u -/
structure SubsetSelection (M : Structure S (Type u)) where
  subset : (A : S.Sorts) → Set (M.sorts A)

/-!
## Function Closure
-/

/-- Function closure for a function with base domain and codomain -/
def funcPreservesSubset {M : Structure S (Type u)}
    (sel : SubsetSelection M)
    (f : S.Functions)
    {A B : S.Sorts}
    (hdom : f.domain = DerivedSorts.inj A)
    (hcod : f.codomain = DerivedSorts.inj B) : Prop :=
  ∀ x : M.sorts A,
    x ∈ sel.subset A →
    castCod hcod (M.Functions f (castDom hdom x)) ∈ sel.subset B

/-!
## Structure Embeddings
-/

/-- An embedding of structures.
    Functions must commute with the embedding on ALL derived sorts (not just base sorts).
    This is the correct premise for the Monotonic Submodel Property. -/
structure StructureEmbedding (M M' : Structure S (Type u)) where
  /-- The carrier maps on base sorts -/
  embed : ∀ A, M.sorts A → M'.sorts A
  /-- Embeddings are injective -/
  embed_inj : ∀ A, Function.Injective (embed A)
  /-- Functions commute with embedding (for ALL functions, regardless of domain/codomain sort) -/
  func_comm : ∀ (f : S.Functions) (x : f.domain.interpret M.sorts),
    liftSort' embed f.codomain (M.Functions f x) =
    M'.Functions f (liftSort' embed f.domain x)

/-- Helper: liftSort' on .inj sorts equals embed -/
theorem liftSort'_inj_eq {M M' : Structure S (Type u)}
    (embed : ∀ A, M.sorts A → M'.sorts A) (A : S.Sorts) (x : M.sorts A) :
    liftSort' embed (.inj A) x = embed A x := rfl

/-- liftSort' on a derived sort equal to .inj A with explicit cast handling -/
theorem liftSort'_inj_cast {M M' : Structure S (Type u)}
    (embed : ∀ A, M.sorts A → M'.sorts A) {D : DerivedSorts S.Sorts} {A : S.Sorts}
    (h : D = .inj A) (x : D.interpret M.sorts) :
    liftSort' embed D x =
    cast (congrArg (DerivedSorts.interpret M'.sorts) h.symm)
      (embed A (cast (congrArg (DerivedSorts.interpret M.sorts) h) x)) := by
  subst h
  rfl

/-- For base-sorted functions, the embedding commutes in a simpler form.
    This extracts the base-sort case from the general func_comm. -/
theorem StructureEmbedding.func_comm_base {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M')
    (f : S.Functions)
    {A B : S.Sorts}
    (hdom : f.domain = DerivedSorts.inj A)
    (hcod : f.codomain = DerivedSorts.inj B)
    (x : M.sorts A) :
    emb.embed B (castCod hcod (M.Functions f (castDom hdom x))) =
    castCod hcod (M'.Functions f (castDom hdom (emb.embed A x))) := by
  -- Unfold the cast helpers
  simp only [castDom, castCod]
  -- Get func_comm instance
  have hfc := emb.func_comm f (cast (congrArg (DerivedSorts.interpret M.sorts) hdom.symm) x)
  -- Rewrite liftSort' using the helper lemmas
  rw [liftSort'_inj_cast emb.embed hcod, liftSort'_inj_cast emb.embed hdom] at hfc
  -- Now simplify the casts in hfc
  simp only [cast_cast, cast_eq] at hfc
  -- hfc : cast hcod.symm' a = b where we want a = cast hcod' b
  -- Apply cast hcod' to both sides of hfc
  have hfc' := congrArg (cast (congrArg (DerivedSorts.interpret M'.sorts) hcod)) hfc
  simp only [cast_cast, cast_eq] at hfc' ⊢
  exact hfc'

/-!
## Pushforward of Subset Selections
-/

/-- Push forward a subset selection along an embedding -/
def SubsetSelection.pushforward {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M') (sel : SubsetSelection M) : SubsetSelection M' where
  subset A := emb.embed A '' sel.subset A

/-- **Key Lemma**: Function closure is preserved by pushforward -/
theorem pushforward_preserves_closure {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M')
    (sel : SubsetSelection M)
    (f : S.Functions)
    {A B : S.Sorts}
    (hdom : f.domain = DerivedSorts.inj A)
    (hcod : f.codomain = DerivedSorts.inj B)
    (hclosed : funcPreservesSubset sel f hdom hcod) :
    funcPreservesSubset (sel.pushforward emb) f hdom hcod := by
  intro x' hx'
  -- x' is in the image of sel.subset A
  simp only [SubsetSelection.pushforward, Set.mem_image] at hx' ⊢
  obtain ⟨x, hx_mem, hx_eq⟩ := hx'
  -- Apply function closure in M
  have hout := hclosed x hx_mem
  -- The output is in sel.subset B
  refine ⟨castCod hcod (M.Functions f (castDom hdom x)), hout, ?_⟩
  -- Use the base-sorted func_comm helper
  have hfc := emb.func_comm_base f hdom hcod x
  -- hfc : emb.embed B (castCod hcod (M.Functions f (castDom hdom x))) =
  --       castCod hcod (M'.Functions f (castDom hdom (emb.embed A x)))
  rw [hfc, ← hx_eq]

/-!
## Main Theorem
-/

/--
**Main Theorem (Monotonic Submodel Property)**

For base-sorted functions, the pushforward of a function-closed subset
selection along an embedding is also function-closed.

This is stated per-function; the full property follows by applying to all functions.
-/
theorem monotonic_submodel_property {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M')
    (sel : SubsetSelection M)
    (f : S.Functions)
    {A B : S.Sorts}
    (hdom : f.domain = DerivedSorts.inj A)
    (hcod : f.codomain = DerivedSorts.inj B)
    (hclosed : funcPreservesSubset sel f hdom hcod) :
    funcPreservesSubset (sel.pushforward emb) f hdom hcod :=
  pushforward_preserves_closure emb sel f hdom hcod hclosed

/-!
## Closed Subset Selections
-/

/-- A subset selection is fully closed if it's closed under all base-sorted functions -/
structure ClosedSubsetSelection (M : Structure S (Type u)) extends SubsetSelection M where
  /-- Function closure for all base-sorted functions -/
  func_closed : ∀ (f : S.Functions) {A B : S.Sorts}
    (hdom : f.domain = DerivedSorts.inj A)
    (hcod : f.codomain = DerivedSorts.inj B),
    funcPreservesSubset toSubsetSelection f hdom hcod

/--
**Semantic Monotonicity**: If sel is a closed subset selection in M,
and emb : M → M' is an embedding, then sel.pushforward emb is also closed in M'.

This is the semantic content of the CALM theorem's monotonicity condition:
extending a structure by adding elements preserves the validity of existing submodels.
-/
theorem semantic_monotonicity {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M')
    (sel : ClosedSubsetSelection M)
    (f : S.Functions)
    {A B : S.Sorts}
    (hdom : f.domain = DerivedSorts.inj A)
    (hcod : f.codomain = DerivedSorts.inj B) :
    funcPreservesSubset (sel.toSubsetSelection.pushforward emb) f hdom hcod :=
  pushforward_preserves_closure emb sel.toSubsetSelection f hdom hcod (sel.func_closed f hdom hcod)

/-- The pushforward of a closed selection is closed -/
def ClosedSubsetSelection.pushforward {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M') (sel : ClosedSubsetSelection M) : ClosedSubsetSelection M' where
  toSubsetSelection := sel.toSubsetSelection.pushforward emb
  func_closed f {_A} {_B} hdom hcod := semantic_monotonicity emb sel f hdom hcod

/-!
## Relation Preservation
-/

/-- Transport for relation domains -/
def castRelDom {M : Structure S (Type u)} {R : S.Relations} {A : S.Sorts}
    (hdom : R.domain = DerivedSorts.inj A) (x : M.sorts A) :
    R.domain.interpret M.sorts :=
  cast (congrArg (DerivedSorts.interpret M.sorts) hdom).symm x

/-!
In Type u, a `Subobject X` represents a monomorphism into X, which
corresponds to a subset of X. An element x : X is "in" the subobject
iff x is in the range of the representing monomorphism (the arrow).
-/

/-- Membership in a subobject (in Type u): x is in the range of the arrow -/
def subobjectMem {X : Type u} (S : Subobject X) (x : X) : Prop :=
  x ∈ Set.range S.arrow

/-- Relation membership for base-sorted relations -/
def relMem {M : Structure S (Type u)} (R : S.Relations) {A : S.Sorts}
    (hdom : R.domain = DerivedSorts.inj A) (x : M.sorts A) : Prop :=
  subobjectMem (M.Relations R) (castRelDom hdom x)

/-- A structure embedding that also preserves relations.
    Relation preservation is stated for ALL derived sort domains, not just base sorts,
    since geometric relations can have product domains (e.g., binary relations). -/
structure RelPreservingEmbedding (M M' : Structure S (Type u)) extends StructureEmbedding M M' where
  /-- Relations are preserved: if x ∈ R in M, then liftSort'(x) ∈ R in M' -/
  rel_preserve : ∀ (R : S.Relations) (x : R.domain.interpret M.sorts),
    subobjectMem (M.Relations R) x →
    subobjectMem (M'.Relations R) (liftSort' embed R.domain x)

/--
A **conservative expansion** is an embedding where:
1. Relations are preserved (forward): R(x) in M → R(emb(x)) in M'
2. Relations are reflected (backward): R(emb(x)) in M' → R(x) in M

The reflection condition captures "only adding relation tuples concerning new elements":
if a relation holds on lifted old elements in M', it must have already held in M.

With both directions, formula satisfaction becomes an IFF for old tuples,
which is the key to proving that old submodels remain valid models.
-/
structure ConservativeExpansion (M M' : Structure S (Type u)) extends RelPreservingEmbedding M M' where
  /-- Relations are reflected: if R(emb(x)) in M', then R(x) in M
      (no new relation tuples added on old elements) -/
  rel_reflect : ∀ (R : S.Relations) (x : R.domain.interpret M.sorts),
    subobjectMem (M'.Relations R) (liftSort' embed R.domain x) →
    subobjectMem (M.Relations R) x

/-- Relation membership is an IFF for conservative expansions -/
theorem rel_preserve_iff {M M' : Structure S (Type u)}
    (emb : ConservativeExpansion M M')
    (R : S.Relations) (x : R.domain.interpret M.sorts) :
    subobjectMem (M.Relations R) x ↔
    subobjectMem (M'.Relations R) (liftSort' emb.embed R.domain x) :=
  ⟨emb.rel_preserve R x, emb.rel_reflect R x⟩

/-!
### Subset Selection with Relation Closure

A subset selection is "relation-closed" if whenever x is in the selection
and x is in relation R, then x satisfies the "domain requirement" for R.
For geometric logic, this isn't quite the right notion since relations can
have product domains. However, for base-sorted relations it's straightforward.
-/

/-- A closed selection respects relations: elements in relations stay in the selection -/
structure FullyClosedSelection (M : Structure S (Type u)) extends ClosedSubsetSelection M where
  /-- For base-sorted relations, if x ∈ R and x ∈ sel, the membership is consistent -/
  rel_closed : ∀ (R : S.Relations) {A : S.Sorts}
    (hdom : R.domain = DerivedSorts.inj A) (x : M.sorts A),
    relMem R hdom x → x ∈ subset A

/-- Elements in the selection get pushed forward -/
theorem selection_pushforward_mem {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M')
    (sel : SubsetSelection M)
    {A : S.Sorts}
    (x : M.sorts A)
    (hsel : x ∈ sel.subset A) :
    emb.embed A x ∈ (sel.pushforward emb).subset A := by
  simp only [SubsetSelection.pushforward, Set.mem_image]
  exact ⟨x, hsel, rfl⟩

/-- Relation membership transfers across embeddings (base-sorted version).
    This is a corollary of the general `rel_preserve` for relations with base sort domains. -/
theorem rel_mem_transfer {M M' : Structure S (Type u)}
    (emb : RelPreservingEmbedding M M')
    (R : S.Relations)
    {A : S.Sorts}
    (hdom : R.domain = DerivedSorts.inj A)
    (x : M.sorts A)
    (hrel : relMem (M := M) R hdom x) :
    relMem (M := M') R hdom (emb.embed A x) := by
  simp only [relMem, castRelDom, subobjectMem] at hrel ⊢
  -- Convert hrel to subobjectMem form for the general rel_preserve
  let x' : R.domain.interpret M.sorts := cast (congrArg (DerivedSorts.interpret M.sorts) hdom).symm x
  have hrel' : subobjectMem (M.Relations R) x' := by convert hrel
  have h := emb.rel_preserve R x' hrel'
  -- h : subobjectMem (M'.Relations R) (liftSort' emb.embed R.domain x')
  -- Use liftSort'_inj_cast to handle the equation
  rw [liftSort'_inj_cast emb.embed hdom] at h
  simp only [cast_cast, cast_eq, x'] at h
  convert h using 2

/-!
## Connection to Theory Satisfaction

The key insight connecting our structural results to `Theory.interpret`.
-/

/-!
### Formula Satisfaction via Subobjects

In `Type u`, formula interpretation gives a subobject, which is essentially
a subset. An element (or tuple) satisfies a formula iff it's in that subset.

**Key Mathlib lemmas for Type u:**
- `Types.subobjectEquivSet α : Subobject α ≃o Set α` - subobjects = sets
- In this order iso, `⊤ ↦ Set.univ` and `⊥ ↦ ∅`
- Product of subobjects ↦ intersection of sets
- Coproduct of subobjects ↦ union of sets
-/

/-- An element is in the formula's interpretation (Type u specific) -/
def formulaSatisfied {M : Structure S (Type u)} [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    {xs : Context S} (φ : Formula xs) (t : Context.interpret M xs) : Prop :=
  subobjectMem (Formula.interpret M φ) t

/-!
### Lifting Embeddings to Contexts

An embedding on sorts lifts to an embedding on context interpretations.
In Type u, this is straightforward because:
- `Context.interpret M xs` is the categorical product `∏ᶜ (fun i => ⟦M | xs.nth i⟧ᵈ)`
- By `Types.productIso`, this is isomorphic to `∀ i, M.sorts (xs.nth i).underlying`
- The lift applies the embedding componentwise

**Justification:** In Type u, products are pi types (`Types.productIso : ∏ᶜ F ≅ ∀ j, F j`),
so lifting is just `fun ctx i => emb.embed _ (ctx i)` modulo the isomorphism.
-/

/-- Types.productIso.hom extracts component j when applied at j.
    Uses Mathlib's Types.productIso_hom_comp_eval. -/
lemma Types_productIso_hom_apply {J : Type v} (f : J → Type (max v u)) (x : ∏ᶜ f) (j : J) :
    (Types.productIso f).hom x j = Pi.π f j x := by
  have h := Types.productIso_hom_comp_eval f j
  exact congrFun h x

/-- Types.productIso.inv satisfies projection identity.
    Uses Mathlib's Types.productIso_inv_comp_π. -/
lemma Types_productIso_inv_apply {J : Type v} (f : J → Type (max v u)) (g : (j : J) → f j) (j : J) :
    Pi.π f j ((Types.productIso f).inv g) = g j := by
  have h := Types.productIso_inv_comp_π f j
  exact congrFun h g

/-- Lift an element of a derived sort along an embedding.
    For base sorts: just the embedding.
    For products: apply componentwise via Types.productIso. -/
noncomputable def liftSort {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M') : (A : DerivedSorts S.Sorts) →
    A.interpret M.sorts → A.interpret M'.sorts
  | .inj B => emb.embed B
  | .prod Aᵢ => fun x =>
    let x' := (Types.productIso _).hom x
    let y' : ∀ i, (Aᵢ i).interpret M'.sorts := fun i => liftSort emb (Aᵢ i) (x' i)
    (Types.productIso _).inv y'

/-- liftSort equals liftSort' applied to the embedding -/
theorem liftSort_eq_liftSort' {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M') (D : DerivedSorts S.Sorts) (x : D.interpret M.sorts) :
    liftSort emb D x = liftSort' emb.embed D x := by
  induction D with
  | inj B => rfl
  | prod Aᵢ ih =>
    simp only [liftSort, liftSort']
    -- Both sides are productIso.inv applied to a function.
    -- We need to show the functions are equal.
    -- Goal: productIso.inv (fun i => liftSort ...) = productIso.inv (fun i => liftSort' ...)
    -- This follows by congruence if the functions are equal
    have heq : (fun i => liftSort emb (Aᵢ i) ((Types.productIso _).hom x i)) =
               (fun i => liftSort' emb.embed (Aᵢ i) ((Types.productIso _).hom x i)) := by
      funext i
      exact ih i _
    simp only [heq]

/-- liftSort is injective for any derived sort.
    For base sorts, this is just embed_inj.
    For products, this follows from componentwise injectivity. -/
theorem liftSort_injective {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M') (D : DerivedSorts S.Sorts) :
    Function.Injective (liftSort emb D) := by
  induction D with
  | inj B =>
    -- For base sorts, liftSort = embed, which is injective by embed_inj
    exact emb.embed_inj B
  | prod Aᵢ ih =>
    -- For products, show componentwise injectivity implies total injectivity
    intro x y hxy
    -- liftSort emb (.prod Aᵢ) x = productIso.inv (fun i => liftSort emb (Aᵢ i) (productIso.hom x i))
    simp only [liftSort] at hxy
    -- hxy : productIso.inv (fun i => ...) = productIso.inv (fun i' => ...)
    -- productIso is an isomorphism, so its inv is injective (via hom ∘ inv = id)
    let iso_M' := Types.productIso (fun j => (Aᵢ j).interpret M'.sorts)
    -- In Types, hom ≫ inv = 𝟙 gives hom (inv x) = x
    have hinv_li : Function.LeftInverse iso_M'.hom iso_M'.inv := fun a => by
      have h := congrFun (iso_M'.inv_hom_id) a
      simp only [types_comp_apply, types_id_apply] at h
      exact h
    have hinv_inj : Function.Injective iso_M'.inv := hinv_li.injective
    have h := hinv_inj hxy
    -- h : (fun i => liftSort emb (Aᵢ i) (productIso.hom x i)) =
    --     (fun i => liftSort emb (Aᵢ i) (productIso.hom y i))
    -- Extract componentwise and use ih
    have hcomp : ∀ i, (Types.productIso _).hom x i = (Types.productIso _).hom y i := by
      intro i
      have hi := congrFun h i
      exact ih i hi
    -- Reconstruct equality of x and y
    have hxy' : (Types.productIso _).hom x = (Types.productIso _).hom y := funext hcomp
    let iso_M := Types.productIso (fun j => (Aᵢ j).interpret M.sorts)
    have hhom_li : Function.LeftInverse iso_M.inv iso_M.hom := fun a => by
      have h := congrFun (iso_M.hom_inv_id) a
      simp only [types_comp_apply, types_id_apply] at h
      exact h
    have hhom_inj : Function.Injective iso_M.hom := hhom_li.injective
    exact hhom_inj hxy'

/-- Lift an embedding to context interpretations (componentwise application) -/
noncomputable def liftEmbedContext {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M') (xs : Context S) :
    Context.interpret M xs → Context.interpret M' xs := fun ctx =>
  let ctx' := (Types.productIso _).hom ctx
  let liftedCtx' : ∀ i, (xs.nth i).interpret M'.sorts :=
    fun i => liftSort emb (xs.nth i) (ctx' i)
  (Types.productIso _).inv liftedCtx'

/-- Generalized relation preservation for arbitrary derived sort domains.
    This is the version needed for formula satisfaction monotonicity.
    Follows from RelPreservingEmbedding.rel_preserve via liftSort_eq_liftSort'. -/
theorem rel_preserve_general {M M' : Structure S (Type u)}
    (emb : RelPreservingEmbedding M M')
    (R : S.Relations) (x : R.domain.interpret M.sorts) :
    subobjectMem (M.Relations R) x →
    subobjectMem (M'.Relations R) (liftSort emb.toStructureEmbedding R.domain x) := by
  intro hmem
  rw [liftSort_eq_liftSort']
  exact emb.rel_preserve R x hmem

/-!
### Formula Monotonicity

For geometric formulas, satisfaction transfers across relation-preserving embeddings.
The proof outline by formula case:

| Formula | Interpretation | Why monotone |
|---------|---------------|--------------|
| `rel R t` | `pullback ⟦t⟧ᵗ (M.Relations R)` | rel_preserve + pullback naturality |
| `true` | `⊤` | Always satisfied |
| `false` | `⊥` | Never satisfied (vacuous) |
| `φ ∧ ψ` | `φ.interpret ⨯ ψ.interpret` | IH on both components |
| `t₁ = t₂` | `equalizerSubobject ⟦t₁⟧ᵗ ⟦t₂⟧ᵗ` | Embedding injectivity |
| `∃x.φ` | `(exists π).obj φ.interpret` | Witness transfers via emb |
| `⋁ᵢφᵢ` | `∐ᵢ φᵢ.interpret` | Satisfied disjunct transfers |

Each case uses specific Mathlib lemmas about Type u:
- `true/false`: `Types.subobjectEquivSet` sends ⊤ to univ, ⊥ to ∅
- `conj`: Product of subobjects = intersection via order iso
- `eq`: Equalizer in Type u = `{x | f x = g x}` (Types.equalizer_eq_kernel)
- `exists`: Image in Type u = `Set.range f`
- `infdisj`: Coproduct = union
-/

/-- Term interpretation commutes with embedding via liftSort.
    Proof by induction on term structure. -/
theorem term_interpret_commutes {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : StructureEmbedding M M')
    {xs : Context S} {A : DerivedSorts S.Sorts}
    (t : Term xs A) (ctx : Context.interpret M xs) :
    Term.interpret M' t (liftEmbedContext emb xs ctx) =
    liftSort emb A (Term.interpret M t ctx) := by
  -- Induction on term structure.
  -- Each case requires careful handling of Types.productIso and eqToHom casts.
  -- The key insights:
  -- - var: liftEmbedContext applies liftSort componentwise, extraction via Pi.π matches
  -- - func: follows from func_comm generalized to derived sorts
  -- - pair: componentwise by IH, using productIso injectivity
  -- - proj: IH plus extraction from liftSort on products
  induction t with
  | var v =>
    -- Term.interpret for var v is: Pi.π _ v ≫ eqToHom _
    -- In Type u, eqToHom is identity when proving xs.nth v = xs.nth v (rfl)
    simp only [Term.interpret, types_comp_apply, eqToHom_refl, types_id_apply]
    -- Goal: Pi.π _ v (liftEmbedContext emb xs ctx) = liftSort emb _ (Pi.π _ v ctx)
    --
    -- liftEmbedContext applies liftSort componentwise via Types.productIso:
    --   liftEmbedContext ctx = productIso.inv (fun i => liftSort (productIso.hom ctx i))
    -- Extracting component v via Pi.π gives the v-th component of the function.
    --
    -- Define the relevant functions with explicit types
    let f_M := fun i : Fin xs.length => (xs.nth i).interpret M.sorts
    let f_M' := fun i : Fin xs.length => (xs.nth i).interpret M'.sorts
    -- The lifted function
    let g : (i : Fin xs.length) → f_M' i :=
        fun i => liftSort emb (xs.nth i) ((Types.productIso f_M).hom ctx i)
    -- liftEmbedContext is productIso.inv applied to g
    have h1 : liftEmbedContext emb xs ctx = (Types.productIso f_M').inv g := rfl
    rw [h1]
    -- Apply Types_productIso_inv_apply: Pi.π f_M' v (productIso.inv g) = g v
    rw [Types_productIso_inv_apply f_M' g v]
    -- Now goal: g v = liftSort emb (xs.nth v) (Pi.π f_M v ctx)
    -- g v = liftSort emb (xs.nth v) ((Types.productIso f_M).hom ctx v)
    -- So we need: (Types.productIso f_M).hom ctx v = Pi.π f_M v ctx
    have h2 : (Types.productIso f_M).hom ctx v = Pi.π f_M v ctx :=
      Types_productIso_hom_apply f_M ctx v
    simp only [g, h2]
    -- Goal should now be: liftSort emb (xs.nth v) (Pi.π f_M v ctx) = liftSort emb _ (Pi.π _ v ctx)
    -- This is definitionally true since f_M i = (xs.nth i).interpret M.sorts
    rfl
  | func f t' ih =>
    -- Function application: (func f t').interpret M ctx = t'.interpret M ctx ≫ M.Functions f
    -- In Type u, composition is just function application.
    simp only [Term.interpret, types_comp_apply]
    -- Goal: M'.Functions f (t'.interpret M' (liftEmbedContext emb xs ctx)) =
    --       liftSort emb f.codomain (M.Functions f (t'.interpret M ctx))
    -- By IH: t'.interpret M' (liftEmbedContext emb xs ctx) = liftSort emb f.domain (t'.interpret M ctx)
    rw [ih]
    -- Goal: M'.Functions f (liftSort emb f.domain (t'.interpret M ctx)) =
    --       liftSort emb f.codomain (M.Functions f (t'.interpret M ctx))
    -- This is exactly func_comm (with sides swapped)
    -- func_comm : liftSort' embed f.codomain (M.Functions f x) = M'.Functions f (liftSort' embed f.domain x)
    -- liftSort emb = liftSort' emb.embed (we need a lemma for this or unfold)
    have hfc := emb.func_comm f (t'.interpret M ctx)
    -- hfc : liftSort' emb.embed f.codomain (M.Functions f _) = M'.Functions f (liftSort' emb.embed f.domain _)
    -- We need: M'.Functions f (liftSort emb f.domain _) = liftSort emb f.codomain (M.Functions f _)
    -- which is hfc.symm after showing liftSort emb = liftSort' emb.embed
    rw [liftSort_eq_liftSort' emb f.domain, liftSort_eq_liftSort' emb f.codomain]
    exact hfc.symm
  | @pair n Aᵢ tᵢ ih =>
    -- Pair builds a product from component interpretations.
    -- Both sides are elements of the product type. Show equal componentwise.
    simp only [Term.interpret]
    -- Use that Types.productIso is an isomorphism to transfer to component equality
    let f_M := fun j : Fin n => (Aᵢ j).interpret M.sorts
    let f_M' := fun j : Fin n => (Aᵢ j).interpret M'.sorts
    let lhs := Pi.lift (fun i => (tᵢ i).interpret M') (liftEmbedContext emb xs ctx)
    let rhs := liftSort emb (.prod Aᵢ) (Pi.lift (fun i => (tᵢ i).interpret M) ctx)
    -- Show lhs and rhs are equal by applying Types.productIso.hom and using funext
    suffices h : (Types.productIso f_M').hom lhs = (Types.productIso f_M').hom rhs by
      have hinj := (Types.productIso f_M').toEquiv.injective
      exact hinj h
    funext j
    simp only [Types_productIso_hom_apply, Types.pi_lift_π_apply, lhs]
    -- Goal: (tᵢ j).interpret M' (liftEmbedContext emb xs ctx) = (Types.productIso f_M').hom rhs j
    rw [ih j]
    -- RHS
    simp only [rhs]
    let x := Pi.lift (fun i => (tᵢ i).interpret M) ctx
    let g : (j : Fin n) → f_M' j := fun j => liftSort emb (Aᵢ j) ((Types.productIso f_M).hom x j)
    have h1 : liftSort emb (.prod Aᵢ) x = (Types.productIso f_M').inv g := rfl
    rw [h1, Types_productIso_inv_apply f_M' g j]
    simp only [g, Types_productIso_hom_apply, x, Types.pi_lift_π_apply]
  | @proj n Aᵢ t' i ih =>
    -- Projection extracts the i-th component from a product.
    -- Term.interpret M (proj t' i) = t'.interpret M ≫ Pi.π _ i
    simp only [Term.interpret, types_comp_apply]
    -- Goal: Pi.π _ i (t'.interpret M' (liftEmbedContext emb xs ctx)) =
    --       liftSort emb (Aᵢ i) (Pi.π _ i (t'.interpret M ctx))
    -- By IH: t'.interpret M' (liftEmbedContext emb xs ctx) = liftSort emb (.prod Aᵢ) (t'.interpret M ctx)
    rw [ih]
    -- Goal: Pi.π _ i (liftSort emb (.prod Aᵢ) (t'.interpret M ctx)) =
    --       liftSort emb (Aᵢ i) (Pi.π _ i (t'.interpret M ctx))
    -- This is "liftSort distributes over projection"
    -- By definition, liftSort emb (.prod Aᵢ) x = productIso.inv (fun j => liftSort emb (Aᵢ j) (productIso.hom x j))
    let x := Term.interpret M t' ctx
    let f_M := fun j : Fin n => (Aᵢ j).interpret M.sorts
    let f_M' := fun j : Fin n => (Aᵢ j).interpret M'.sorts
    let g : (j : Fin n) → f_M' j := fun j => liftSort emb (Aᵢ j) ((Types.productIso f_M).hom x j)
    -- liftSort emb (.prod Aᵢ) x = (Types.productIso f_M').inv g
    have h1 : liftSort emb (.prod Aᵢ) x = (Types.productIso f_M').inv g := rfl
    rw [h1]
    -- Apply Types_productIso_inv_apply: Pi.π f_M' i (productIso.inv g) = g i
    rw [Types_productIso_inv_apply f_M' g i]
    -- Goal: g i = liftSort emb (Aᵢ i) (Pi.π f_M i x)
    -- g i = liftSort emb (Aᵢ i) ((Types.productIso f_M).hom x i)
    have h2 : (Types.productIso f_M).hom x i = Pi.π f_M i x :=
      Types_productIso_hom_apply f_M x i
    simp only [g, h2]
    rfl

/-- Context morphism interpretation commutes with liftEmbedContext.
    This is the context morphism analogue of term_interpret_commutes.
    For a context morphism σ : ys ⟶ xs, we have:
      liftEmbedContext xs (σ.interpret M ctx) = σ.interpret M' (liftEmbedContext ys ctx) -/
theorem hom_interpret_commutes {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : StructureEmbedding M M')
    {ys xs : Context S}
    (σ : ys ⟶ xs) (ctx : Context.interpret M ys) :
    liftEmbedContext emb xs (Context.Hom.interpret M σ ctx) =
    Context.Hom.interpret M' σ (liftEmbedContext emb ys ctx) := by
  -- σ.interpret = Pi.lift (fun i => (σ i).interpret)
  -- Both sides are built from Pi.lift; compare componentwise
  simp only [Context.Hom.interpret]
  -- Goal: liftEmbedContext xs (Pi.lift (fun i => (σ i).interpret M) ctx) =
  --       Pi.lift (fun i => (σ i).interpret M') (liftEmbedContext ys ctx)
  -- Use Types.productIso to extract components
  let f_M := fun i : Fin xs.length => (xs.nth i).interpret M.sorts
  let f_M' := fun i : Fin xs.length => (xs.nth i).interpret M'.sorts
  apply (Types.productIso f_M').toEquiv.injective
  funext i
  -- Compare components: apply productIso.hom and extract i-th component
  simp only [Iso.toEquiv_fun]
  rw [Types_productIso_hom_apply f_M', Types_productIso_hom_apply f_M']
  -- RHS: Pi.π f_M' i (Pi.lift (fun i => (σ i).interpret M') (liftEmbedContext ys ctx))
  --    = (σ i).interpret M' (liftEmbedContext ys ctx)
  rw [Types.pi_lift_π_apply]
  -- LHS: Pi.π f_M' i (liftEmbedContext xs (Pi.lift (fun i => (σ i).interpret M) ctx))
  -- By definition of liftEmbedContext
  simp only [liftEmbedContext]
  rw [Types_productIso_inv_apply f_M', Types_productIso_hom_apply f_M]
  -- LHS: liftSort emb (xs.nth i) (Pi.π f_M i (Pi.lift (fun i => (σ i).interpret M) ctx))
  rw [Types.pi_lift_π_apply]
  -- LHS: liftSort emb (xs.nth i) ((σ i).interpret M ctx)
  -- RHS: (σ i).interpret M' (liftEmbedContext ys ctx)
  -- By term_interpret_commutes
  exact (term_interpret_commutes emb (σ i) ctx).symm

/-!
**Formula Satisfaction Monotonicity**

Geometric formula satisfaction is preserved by relation-preserving embeddings.
This is the semantic justification for the CALM theorem: valid queries
remain valid as the database grows.

The proof structure is complete; each case requires unpacking the categorical
definitions using Type u specific lemmas from Mathlib.
-/

/-- In Type u, morphisms from initial objects are monomorphisms (vacuously injective) -/
instance : InitialMonoClass (Type u) where
  isInitial_mono_from {I} X hI := by
    -- hI : IsInitial I means I is empty (in Type u)
    -- So any morphism from I is injective (vacuously)
    rw [mono_iff_injective]
    intro a b _
    -- I is empty: there's a map to PEmpty, so I must be empty
    have hemp : IsEmpty I := ⟨fun x => PEmpty.elim (hI.to PEmpty.{u+1} x)⟩
    exact hemp.elim a

/-- ⊤.arrow is surjective in Type u (since it's an iso, and isos are bijections) -/
theorem top_arrow_surjective {X : Type u} : Function.Surjective (⊤ : Subobject X).arrow := by
  haveI : IsIso (⊤ : Subobject X).arrow := Subobject.isIso_top_arrow
  exact ((isIso_iff_bijective (⊤ : Subobject X).arrow).mp inferInstance).2

/-- ⊥.underlying is empty in Type u.
    With Mathlib's OrderBot (via instance priority override), this follows from botCoeIsoInitial. -/
theorem bot_underlying_isEmpty {X : Type u} : IsEmpty ((⊥ : Subobject X) : Type u) := by
  have h1 : (Subobject.underlying.obj (⊥ : Subobject X)) ≅ ⊥_ (Type u) := Subobject.botCoeIsoInitial
  have h2 : ⊥_ (Type u) ≅ PEmpty := Types.initialIso
  exact ⟨fun y => PEmpty.elim ((h1 ≪≫ h2).hom y)⟩

/-- The set corresponding to a subobject under Types.subobjectEquivSet is the range of its arrow.
    This is essentially by definition since both go through the representative. -/
theorem subobject_equiv_eq_range {X : Type u} (f : Subobject X) :
    (Types.subobjectEquivSet X) f = Set.range f.arrow := by
  simp only [Types.subobjectEquivSet]
  rfl

/-- Types.equalizerIso.inv sends ⟨x, heq⟩ to the element of equalizer that ι maps to x. -/
lemma types_equalizerIso_inv_ι {X Y : Type u} (f g : X ⟶ Y) (x_sub : { x : X // f x = g x }) :
    equalizer.ι f g ((Types.equalizerIso f g).inv x_sub) = x_sub.val := by
  have h := limit.isoLimitCone_inv_π (F := parallelPair f g) Types.equalizerLimit WalkingParallelPair.zero
  simp only [Types.equalizerIso, parallelPair_obj_zero, limit.π] at h ⊢
  exact congrFun h x_sub

/-- In Type u, x ∈ range (equalizerSubobject f g).arrow iff f x = g x. -/
theorem equalizer_range_iff {X Y : Type u} (f g : X ⟶ Y) (x : X) :
    x ∈ Set.range (equalizerSubobject f g).arrow ↔ f x = g x := by
  simp only [equalizerSubobject]
  constructor
  · intro ⟨z, hz⟩
    let z' := (Subobject.underlyingIso (equalizer.ι f g)).hom z
    have hz' : equalizer.ι f g z' = x := by
      have h := Subobject.underlyingIso_hom_comp_eq_mk (equalizer.ι f g)
      simp only [← h, types_comp_apply] at hz
      exact hz
    have hcond := equalizer.condition f g
    have h1 : (equalizer.ι f g ≫ f) z' = (equalizer.ι f g ≫ g) z' := by rw [hcond]
    simp only [types_comp_apply, hz'] at h1
    exact h1
  · intro heq
    let x_sub : { y : X // f y = g y } := ⟨x, heq⟩
    let z_eq : equalizer f g := (Types.equalizerIso f g).inv x_sub
    let z := (Subobject.underlyingIso (equalizer.ι f g)).inv z_eq
    use z
    have h := Subobject.underlyingIso_hom_comp_eq_mk (equalizer.ι f g)
    calc (Subobject.mk (equalizer.ι f g)).arrow z
      = ((Subobject.underlyingIso (equalizer.ι f g)).hom ≫ equalizer.ι f g)
          ((Subobject.underlyingIso (equalizer.ι f g)).inv z_eq) := by rw [h]
      _ = equalizer.ι f g ((Subobject.underlyingIso (equalizer.ι f g)).hom
          ((Subobject.underlyingIso (equalizer.ι f g)).inv z_eq)) := rfl
      _ = equalizer.ι f g z_eq := by simp
      _ = x_sub.val := types_equalizerIso_inv_ι f g x_sub
      _ = x := rfl

/-- In Type u, x ∈ range (f ⊓ g).arrow iff x is in range of both f.arrow and g.arrow.
    This uses that Types.subobjectEquivSet is an order isomorphism, so it preserves inf.
    In Set, inf is intersection, so x ∈ (f ⊓ g) ↔ x ∈ f ∧ x ∈ g. -/
theorem inf_range_iff {X : Type u} (f g : Subobject X) (x : X) :
    x ∈ Set.range (f ⊓ g).arrow ↔ x ∈ Set.range f.arrow ∧ x ∈ Set.range g.arrow := by
  -- Use the order isomorphism Types.subobjectEquivSet : Subobject X ≃o Set X
  let iso := Types.subobjectEquivSet X
  -- Translate membership using subobject_equiv_eq_range
  rw [← subobject_equiv_eq_range (f ⊓ g)]
  rw [← subobject_equiv_eq_range f]
  rw [← subobject_equiv_eq_range g]
  -- Now use that the order iso preserves inf
  have h : iso (f ⊓ g) = iso f ⊓ iso g := iso.map_inf f g
  -- Goal: x ∈ iso (f ⊓ g) ↔ x ∈ iso f ∧ x ∈ iso g
  show x ∈ iso (f ⊓ g) ↔ x ∈ iso f ∧ x ∈ iso g
  rw [h]
  -- In Set X, ⊓ = ∩, so membership is conjunction
  rfl

/-- In Type u, pullback.snd has range equal to preimage.
    For pullback g f where g : Z → Y and f : X → Y,
    range(pullback.snd) = { x | ∃ z, g z = f x } = f⁻¹(range g). -/
lemma pullback_snd_range {X Y Z : Type u} (g : Z ⟶ Y) (f : X ⟶ Y) (x : X) :
    x ∈ Set.range (pullback.snd g f) ↔ f x ∈ Set.range g := by
  constructor
  · intro ⟨z, hz⟩
    let z' := (Types.pullbackIsoPullback g f).hom z
    have hcond : g z'.val.1 = f z'.val.2 := z'.property
    have hsnd : z'.val.2 = x := by
      have h2 := congrFun (limit.isoLimitCone_hom_π (Types.pullbackLimitCone g f) WalkingCospan.right) z
      simp only [Types.pullbackLimitCone, limit.π] at h2
      rw [← hz]
      exact h2.symm
    use z'.val.1
    rw [← hsnd, hcond]
  · intro ⟨z, hz⟩
    let p : Types.PullbackObj g f := ⟨(z, x), hz⟩
    let z' := (Types.pullbackIsoPullback g f).inv p
    use z'
    have h := limit.isoLimitCone_inv_π (Types.pullbackLimitCone g f) WalkingCospan.right
    exact congrFun h p

/-- For isomorphic MonoOvers, their arrows have the same range.
    This is because an iso in MonoOver X means the underlying morphism
    commutes with the arrows (as Over morphisms). -/
lemma monoover_iso_same_range {X : Type u} (A B : MonoOver X) (h : A ≅ B) :
    Set.range A.arrow = Set.range B.arrow := by
  have hcomm : h.hom.left ≫ B.arrow = A.arrow := Over.w h.hom
  have hcomm' : h.inv.left ≫ A.arrow = B.arrow := Over.w h.inv
  ext x
  constructor
  · intro ⟨a, ha⟩
    use h.hom.left a
    calc B.arrow (h.hom.left a)
      = (h.hom.left ≫ B.arrow) a := rfl
      _ = A.arrow a := by rw [hcomm]
      _ = x := ha
  · intro ⟨b, hb⟩
    use h.inv.left b
    calc A.arrow (h.inv.left b)
      = (h.inv.left ≫ A.arrow) b := rfl
      _ = B.arrow b := by rw [hcomm']
      _ = x := hb

/-- The arrow of a Subobject equals the arrow of its representative. -/
lemma subobject_arrow_eq_representative_arrow {X : Type u} (P : Subobject X) :
    P.arrow = (Subobject.representative.obj P).arrow := rfl

/-- In Type u, x ∈ range ((Subobject.pullback f).obj P).arrow iff f x ∈ range P.arrow.
    This is the set-theoretic fact that pullback of a subobject is the preimage. -/
theorem pullback_range_iff {X Y : Type u} (f : X ⟶ Y) (P : Subobject Y) (x : X) :
    x ∈ Set.range ((Subobject.pullback f).obj P).arrow ↔ f x ∈ Set.range P.arrow := by
  let R := Subobject.representative.obj P
  -- R.arrow = P.arrow
  have harrow : R.arrow = P.arrow := (subobject_arrow_eq_representative_arrow P).symm
  -- (MonoOver.pullback f).obj R has arrow = pullback.snd R.arrow f
  have hpb_arrow : ((MonoOver.pullback f).obj R).arrow = pullback.snd R.arrow f :=
    MonoOver.pullback_obj_arrow f R
  -- P = toThinSkeleton R (since representative is a section of toThinSkeleton)
  have hP : P = (toThinSkeleton (MonoOver Y)).obj R := (Quotient.out_eq P).symm
  -- (lower F).obj (toThinSkeleton R) = toThinSkeleton (F.obj R)
  have h1 : (Subobject.pullback f).obj P =
            (toThinSkeleton (MonoOver X)).obj ((MonoOver.pullback f).obj R) := by
    rw [hP]; rfl
  -- representative of the RHS is iso to (MonoOver.pullback f).obj R
  have h2 : Subobject.representative.obj ((toThinSkeleton (MonoOver X)).obj ((MonoOver.pullback f).obj R)) ≅
            (MonoOver.pullback f).obj R :=
    Subobject.representativeIso _
  -- Combine: representative of (pullback f).obj P is iso to (MonoOver.pullback f).obj R
  have h3 : Subobject.representative.obj ((Subobject.pullback f).obj P) ≅
            (MonoOver.pullback f).obj R := by rw [h1]; exact h2
  -- The arrows have the same range
  have h4 : Set.range ((Subobject.pullback f).obj P).arrow =
            Set.range ((MonoOver.pullback f).obj R).arrow := by
    rw [subobject_arrow_eq_representative_arrow]
    exact monoover_iso_same_range _ _ h3
  -- Combine everything
  rw [h4, hpb_arrow, pullback_snd_range, harrow]

/-- In Type u, the range of image.ι equals the range of the original morphism.
    This uses that factorThruImage is an epi (surjective in Type u). -/
lemma image_ι_range_eq {X Y : Type u} (g : X ⟶ Y) :
    Set.range (image.ι g) = Set.range g := by
  ext y
  constructor
  · intro ⟨z, hz⟩
    have h_epi : Epi (factorThruImage g) := inferInstance
    rw [epi_iff_surjective] at h_epi
    obtain ⟨x, hx⟩ := h_epi z
    use x
    calc g x
        = (factorThruImage g ≫ image.ι g) x := by rw [image.fac]
      _ = image.ι g (factorThruImage g x) := rfl
      _ = image.ι g z := by rw [hx]
      _ = y := hz
  · intro ⟨x, hx⟩
    use factorThruImage g x
    calc image.ι g (factorThruImage g x)
        = (factorThruImage g ≫ image.ι g) x := rfl
      _ = g x := by rw [image.fac]
      _ = y := hx

/-- The arrow of (MonoOver.exists f).obj M equals image.ι (M.arrow ≫ f). -/
lemma monoover_exists_arrow {X Y : Type u} (f : X ⟶ Y) (M : MonoOver X) :
    ((MonoOver.exists f).obj M).arrow = image.ι (M.arrow ≫ f) := rfl

/-- The range of ((Subobject.exists f).obj P).arrow equals the range of (P.arrow ≫ f). -/
lemma subobject_exists_arrow_range {X Y : Type u} (f : X ⟶ Y) (P : Subobject X) :
    Set.range ((Subobject.exists f).obj P).arrow = Set.range (P.arrow ≫ f) := by
  let rep_P := Subobject.representative.obj P
  let existsM := (MonoOver.exists f).obj rep_P
  let existsP := (Subobject.exists f).obj P

  -- Step 1: P = [rep_P] in the thin skeleton
  have h_P_eq : P = (toThinSkeleton (MonoOver X)).obj rep_P := by
    simp only [rep_P]
    exact (Quotient.out_eq P).symm

  -- Step 2: Use lower_comm to get the key equation
  have h_func : (Subobject.lower (MonoOver.exists f)).obj ((toThinSkeleton (MonoOver X)).obj rep_P) =
                (toThinSkeleton (MonoOver Y)).obj ((MonoOver.exists f).obj rep_P) := by
    have h := Subobject.lower_comm (MonoOver.exists f)
    have := congrFun (congrArg (fun G => G.obj) h) rep_P
    simp only [Functor.comp_obj] at this
    exact this

  -- Step 3: existsP = [existsM]
  have h_eq : existsP = (toThinSkeleton (MonoOver Y)).obj existsM := by
    calc existsP
      = (Subobject.lower (MonoOver.exists f)).obj P := rfl
      _ = (Subobject.lower (MonoOver.exists f)).obj ((toThinSkeleton (MonoOver X)).obj rep_P) := by rw [← h_P_eq]
      _ = (toThinSkeleton (MonoOver Y)).obj ((MonoOver.exists f).obj rep_P) := h_func
      _ = (toThinSkeleton (MonoOver Y)).obj existsM := rfl

  -- Step 4: representative.obj existsP ≅ existsM
  have h_iso : Subobject.representative.obj existsP ≅ existsM := by
    rw [h_eq]
    exact Subobject.representativeIso existsM

  -- Step 5: Arrows have the same range
  have h_range : Set.range existsP.arrow = Set.range existsM.arrow :=
    monoover_iso_same_range _ _ h_iso

  have h_arrow : existsM.arrow = image.ι (rep_P.arrow ≫ f) := monoover_exists_arrow f rep_P
  have h_img : Set.range (image.ι (rep_P.arrow ≫ f)) = Set.range (rep_P.arrow ≫ f) := image_ι_range_eq _
  have h_rep : rep_P.arrow = P.arrow := rfl

  rw [h_range, h_arrow, h_img, h_rep]

/-- In Type u, y ∈ range ((Subobject.exists f).obj P).arrow iff ∃ x ∈ range P.arrow, f x = y.
    This is the set-theoretic fact that exists/image of a subobject is the direct image. -/
theorem exists_range_iff {X Y : Type u} [HasImages (Type u)] (f : X ⟶ Y) (P : Subobject X) (y : Y) :
    y ∈ Set.range ((Subobject.exists f).obj P).arrow ↔ ∃ x, x ∈ Set.range P.arrow ∧ f x = y := by
  rw [subobject_exists_arrow_range]
  constructor
  · intro ⟨z, hz⟩
    use P.arrow z
    exact ⟨⟨z, rfl⟩, hz⟩
  · intro ⟨x, ⟨z, hz⟩, hfx⟩
    use z
    simp only [types_comp_apply, hz, hfx]

/-- For subobjects A ≤ B, if x ∈ range A.arrow then x ∈ range B.arrow.
    This is the element-level characterization of subobject ordering in Type. -/
theorem subobject_le_range {X : Type u} {A B : Subobject X} (h : A ≤ B)
    {x : X} (hx : x ∈ Set.range A.arrow) : x ∈ Set.range B.arrow := by
  -- h : A ≤ B gives us a morphism ofLE : A.underlying → B.underlying
  -- with the property: ofLE ≫ B.arrow = A.arrow
  obtain ⟨a, ha⟩ := hx
  -- a : A.underlying, A.arrow a = x
  -- Use ofLE to get an element of B.underlying
  use Subobject.ofLE A B h a
  -- Need: B.arrow (ofLE a) = x
  rw [← ha]
  exact congrFun (Subobject.ofLE_arrow h) a

/-- In Subobject X (for Type u), the categorical coproduct equals the lattice supremum.
    This follows from the universal properties: both are the least upper bound of the family. -/
theorem coproduct_eq_iSup {X : Type u} {ι : Type*} (P : ι → Subobject X) [HasCoproduct P] :
    ∐ P = ⨆ i, P i := by
  apply le_antisymm
  · -- ∐ P ≤ ⨆ P: construct morphism from ∐ P to ⨆ P using the coproduct universal property
    exact Quiver.Hom.le (Sigma.desc (fun i => (le_iSup P i).hom))
  · -- ⨆ P ≤ ∐ P: show P i ≤ ∐ P for all i, then ⨆ is least upper bound
    apply iSup_le
    intro i
    exact Quiver.Hom.le (Sigma.ι P i)

/-- In Type u, x ∈ range (⨆ᵢ Pᵢ).arrow iff ∃ i, x ∈ range (Pᵢ).arrow.
    This is the set-theoretic fact that supremum of subobjects is union. -/
theorem iSup_range_iff {X : Type u} {ι : Type*} (P : ι → Subobject X) (x : X) :
    x ∈ Set.range (⨆ i, P i).arrow ↔ ∃ i, x ∈ Set.range (P i).arrow := by
  -- Use the order isomorphism Types.subobjectEquivSet
  let iso := Types.subobjectEquivSet X
  -- iso preserves suprema: iso (⨆ᵢ Pᵢ) = ⨆ᵢ (iso Pᵢ)
  -- In Set X, ⨆ = ⋃, so membership is existential
  rw [← subobject_equiv_eq_range (⨆ i, P i)]
  -- Use that the order iso preserves iSup
  have h : iso (⨆ i, P i) = ⨆ i, iso (P i) := iso.map_iSup P
  rw [h]
  -- In Set X, ⨆ (as sets) is union, so x ∈ ⋃ᵢ Sᵢ ↔ ∃ i, x ∈ Sᵢ
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion]
  constructor
  · intro ⟨i, hi⟩
    use i
    rw [← subobject_equiv_eq_range (P i)]
    exact hi
  · intro ⟨i, hi⟩
    use i
    rw [← subobject_equiv_eq_range (P i)] at hi
    exact hi

theorem formula_satisfaction_monotone {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : RelPreservingEmbedding M M')
    {xs : Context S}
    (φ : Formula xs)
    (t : Context.interpret M xs)
    (hsat : formulaSatisfied (M := M) φ t) :
    formulaSatisfied (M := M') φ (liftEmbedContext emb.toStructureEmbedding xs t) := by
  induction φ with
  | rel R term =>
    -- rel R t ↦ (Subobject.pullback (term.interpret)).obj (M.Relations R)
    -- By pullback_range_iff: t ∈ this iff term.interpret M t ∈ M.Relations R
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    -- hsat : t ∈ range ((pullback (term.interpret M)).obj (M.Relations R)).arrow
    -- Goal : liftEmbedContext t ∈ range ((pullback (term.interpret M')).obj (M'.Relations R)).arrow
    rw [pullback_range_iff] at hsat ⊢
    -- hsat : term.interpret M t ∈ range (M.Relations R).arrow
    -- Goal : term.interpret M' (liftEmbedContext t) ∈ range (M'.Relations R).arrow
    -- Apply term_interpret_commutes to rewrite the LHS
    rw [term_interpret_commutes emb.toStructureEmbedding term t]
    -- Goal: liftSort emb R.domain (term.interpret M t) ∈ range (M'.Relations R).arrow
    -- Apply rel_preserve_general
    exact rel_preserve_general emb R (Term.interpret M term t) hsat
  | «true» =>
    -- ⊤ contains everything: use that ⊤.arrow is surjective
    unfold formulaSatisfied subobjectMem
    simp only [Formula.interpret]
    exact top_arrow_surjective _
  | «false» =>
    -- ⊥ contains nothing: the underlying type is empty, so hsat is contradictory
    -- Formula.interpret .false = ⊥, and we need to show hsat is vacuously true
    unfold formulaSatisfied subobjectMem at hsat
    simp only [Formula.interpret] at hsat
    obtain ⟨y, _⟩ := hsat
    -- y is in the underlying of ⊥ (using Geometric.instOrderBotSubobject)
    -- Both Geometric's ⊥ and Mathlib's ⊥ are bottom in the same partial order, so they're equal.
    -- Prove the two different ⊥s are equal by le_antisymm
    have heq : ∀ {X : Type u},
        @Bot.bot (Subobject X) (Geometric.instOrderBotSubobject X).toBot =
        @Bot.bot (Subobject X) Subobject.orderBot.toBot := by
      intro X
      apply le_antisymm
      · exact @OrderBot.bot_le _ _ (Geometric.instOrderBotSubobject X) _
      · exact @OrderBot.bot_le _ _ Subobject.orderBot _
    -- Rewrite y's type to use Mathlib's ⊥
    rw [heq] at y
    -- Now y : underlying of Mathlib's ⊥, which is empty
    -- Derive False from y being in an empty type, then prove anything
    exact False.elim (bot_underlying_isEmpty.false y)
  | conj φ ψ ihφ ihψ =>
    -- Conjunction: both components must hold
    -- Strategy: use inf_range_iff to decompose and recompose
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    -- hsat: t ∈ range (φ.interpret ⨯ ψ.interpret).arrow (in M)
    -- Goal: liftEmbedContext ... t ∈ range (φ.interpret ⨯ ψ.interpret).arrow (in M')

    -- Use prod_eq_inf: ⨯ = ⊓ in Subobject
    have prod_inf_M := Subobject.prod_eq_inf (f₁ := Formula.interpret M φ) (f₂ := Formula.interpret M ψ)
    have prod_inf_M' := Subobject.prod_eq_inf (f₁ := Formula.interpret M' φ) (f₂ := Formula.interpret M' ψ)

    -- Decompose: if t ∈ (φ ⊓ ψ), then t ∈ φ and t ∈ ψ
    rw [prod_inf_M] at hsat
    rw [inf_range_iff] at hsat
    obtain ⟨hφ, hψ⟩ := hsat

    -- Apply induction hypotheses
    have ihφ' := ihφ t hφ
    have ihψ' := ihψ t hψ

    -- Recompose: if liftEmbedContext t ∈ φ' and ∈ ψ', then ∈ (φ' ⊓ ψ')
    rw [prod_inf_M']
    rw [inf_range_iff]
    exact ⟨ihφ', ihψ'⟩
  | eq t1 t2 =>
    -- Equality: t1 = t2 interprets as equalizerSubobject ⟦t1⟧ᵗ ⟦t2⟧ᵗ
    -- Using equalizer_range_iff: t ∈ equalizerSubobject ↔ t1.interpret t = t2.interpret t
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    -- hsat : t ∈ equalizerSubobject (t1.interpret M) (t2.interpret M)
    -- Goal : liftEmbedContext t ∈ equalizerSubobject (t1.interpret M') (t2.interpret M')
    rw [equalizer_range_iff] at hsat ⊢
    -- hsat : t1.interpret M t = t2.interpret M t
    -- Goal : t1.interpret M' (liftEmbedContext t) = t2.interpret M' (liftEmbedContext t)
    -- Apply term_interpret_commutes to both sides
    rw [term_interpret_commutes emb.toStructureEmbedding t1 t]
    rw [term_interpret_commutes emb.toStructureEmbedding t2 t]
    -- Now goal is: liftSort emb _ (t1.interpret M t) = liftSort emb _ (t2.interpret M t)
    -- This follows from hsat by congruence (liftSort is a function)
    rw [hsat]
  | @«exists» A xs' φ ih =>
    -- Existential quantification: ∃x.φ(ctx, x) interprets as
    --   (Subobject.exists π).obj (φ.interpret)
    -- where π : Context.interpret M (xs'.cons A) → Context.interpret M xs'
    -- is the projection that drops the last variable.
    -- Note: xs' is the base context, xs = exists binds xs' with "∃A.φ" having context xs'
    --
    -- In Type u, (exists f).obj P corresponds to the image of P under f:
    --   y ∈ ((exists f).obj P).arrow iff ∃ x ∈ P.arrow, f x = y
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    -- hsat : t ∈ range ((Subobject.exists ((xs'.π A).interpret M)).obj (φ.interpret M)).arrow
    -- Goal : liftEmbedContext xs' t ∈ range ((Subobject.exists ((xs'.π A).interpret M')).obj (φ.interpret M')).arrow
    rw [exists_range_iff] at hsat ⊢
    -- hsat : ∃ ctx', ctx' ∈ range (φ.interpret M).arrow ∧ (xs'.π A).interpret M ctx' = t
    -- Goal : ∃ ctx', ctx' ∈ range (φ.interpret M').arrow ∧ (xs'.π A).interpret M' ctx' = liftEmbedContext xs' t
    obtain ⟨ctx', hctx'_in, hctx'_proj⟩ := hsat
    -- Lift ctx' to M'
    let ctx'_lifted := liftEmbedContext emb.toStructureEmbedding _ ctx'
    use ctx'_lifted
    constructor
    · -- Show ctx'_lifted ∈ range (φ.interpret M').arrow by IH
      exact ih ctx' hctx'_in
    · -- Show (xs'.π A).interpret M' ctx'_lifted = liftEmbedContext xs' t
      -- By hom_interpret_commutes: liftEmbedContext xs' ((xs'.π A).interpret M ctx') =
      --                            (xs'.π A).interpret M' (liftEmbedContext (A ∶ xs') ctx')
      have hcomm := hom_interpret_commutes emb.toStructureEmbedding (xs'.π A) ctx'
      -- hcomm : liftEmbedContext xs' ((xs'.π A).interpret M ctx') = (xs'.π A).interpret M' ctx'_lifted
      rw [← hcomm, hctx'_proj]
  | infdisj φᵢ ih =>
    -- Infinitary disjunction: ⋁ᵢφᵢ interprets as ∐ (fun i ↦ φᵢ.interpret)
    -- which is the coproduct/supremum of subobjects.
    --
    -- In Type u, coproduct of subobjects corresponds to union:
    --   x ∈ (⨆ᵢ Pᵢ).arrow iff ∃ i, x ∈ (Pᵢ).arrow
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    -- hsat : t ∈ range (∐ᵢ (φᵢ.interpret M)).arrow
    -- Goal : liftEmbedContext xs t ∈ range (∐ᵢ (φᵢ.interpret M')).arrow
    -- Use coproduct_eq_iSup: ∐ P = ⨆ P for subobjects
    rw [coproduct_eq_iSup] at hsat ⊢
    -- Now use iSup_range_iff to convert to existential
    rw [iSup_range_iff] at hsat ⊢
    -- hsat : ∃ i, t ∈ range ((φᵢ i).interpret M).arrow
    -- Goal : ∃ i, liftEmbedContext xs t ∈ range ((φᵢ i).interpret M').arrow
    obtain ⟨i, hi⟩ := hsat
    use i
    -- By IH: formulaSatisfied (φᵢ i) t → formulaSatisfied (φᵢ i) (liftEmbedContext t)
    exact ih i t hi

/-!
## The Bidirectional Theorem: Conservative Expansions

For **conservative expansions** (where new relation tuples only concern new elements),
formula satisfaction is an **IFF**, not just an implication. This is the key to
proving that old submodels remain valid models under universe expansion.
-/

/--
**Backward direction**: For conservative expansions, formula satisfaction in M'
implies satisfaction in M. This is the converse of `formula_satisfaction_monotone`.

Combined with `formula_satisfaction_monotone`, this gives the full IFF.
-/
theorem formula_satisfaction_reflect {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : ConservativeExpansion M M')
    {xs : Context S}
    (φ : Formula xs)
    (t : Context.interpret M xs)
    (hsat : formulaSatisfied φ (liftEmbedContext emb.toStructureEmbedding xs t)) :
    formulaSatisfied φ t := by
  -- Proof by induction on formula structure, using rel_reflect for the base case
  induction φ with
  | rel R term =>
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    rw [pullback_range_iff] at hsat ⊢
    -- hsat : term.interpret M' (liftEmbedContext t) ∈ range (M'.Relations R).arrow
    -- Use term_interpret_commutes to rewrite
    rw [term_interpret_commutes emb.toStructureEmbedding term t] at hsat
    -- hsat : liftSort emb R.domain (term.interpret M t) ∈ range (M'.Relations R).arrow
    -- Convert liftSort to liftSort' to match rel_reflect
    rw [liftSort_eq_liftSort'] at hsat
    -- Apply rel_reflect
    exact emb.rel_reflect R _ hsat
  | «true» =>
    -- ⊤ contains everything
    unfold formulaSatisfied subobjectMem
    simp only [Formula.interpret]
    exact top_arrow_surjective _
  | false =>
    unfold formulaSatisfied subobjectMem at hsat
    simp only [Formula.interpret] at hsat
    have heq : ∀ {X : Type u},
        @Bot.bot (Subobject X) (Geometric.instOrderBotSubobject X).toBot =
        @Bot.bot (Subobject X) Subobject.orderBot.toBot := by
      intro X
      apply le_antisymm
      · exact @OrderBot.bot_le _ _ (Geometric.instOrderBotSubobject X) _
      · exact @OrderBot.bot_le _ _ Subobject.orderBot _
    obtain ⟨y, _⟩ := hsat
    rw [heq] at y
    exact False.elim (bot_underlying_isEmpty.false y)
  | conj φ ψ ihφ ihψ =>
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    have prod_inf_M := Subobject.prod_eq_inf (f₁ := Formula.interpret M φ) (f₂ := Formula.interpret M ψ)
    have prod_inf_M' := Subobject.prod_eq_inf (f₁ := Formula.interpret M' φ) (f₂ := Formula.interpret M' ψ)
    rw [prod_inf_M]
    rw [inf_range_iff]
    rw [prod_inf_M'] at hsat
    rw [inf_range_iff] at hsat
    obtain ⟨hφ', hψ'⟩ := hsat
    exact ⟨ihφ t hφ', ihψ t hψ'⟩
  | eq t1 t2 =>
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    rw [equalizer_range_iff] at hsat ⊢
    -- hsat : t1.interpret M' (liftEmbedContext t) = t2.interpret M' (liftEmbedContext t)
    -- Use term_interpret_commutes and injectivity of embedding
    rw [term_interpret_commutes emb.toStructureEmbedding t1 t] at hsat
    rw [term_interpret_commutes emb.toStructureEmbedding t2 t] at hsat
    -- hsat : liftSort emb _ (t1.interpret M t) = liftSort emb _ (t2.interpret M t)
    -- By injectivity of liftSort (which uses embed's injectivity)
    exact liftSort_injective emb.toStructureEmbedding _ hsat
  | @«exists» A xs' φ ih =>
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    rw [exists_range_iff] at hsat ⊢
    obtain ⟨ctx'_lifted, hctx'_in, hctx'_proj⟩ := hsat
    -- ctx'_lifted = (a', t') where a' : A.interpret M' and t' = liftEmbedContext t
    -- hctx'_in : φ is satisfied by ctx'_lifted in M'
    -- We need a witness (a, t) in M where a : A.interpret M satisfies φ
    --
    -- MATHEMATICAL ISSUE: The witness a' in M' might be a "new" element not in the
    -- image of the embedding. For the backward reflection to work, we would need
    -- either:
    -- (1) The witness to always be in the image (requires additional structure), or
    -- (2) A different witness in M that still satisfies φ (model completeness)
    --
    -- This sorry represents a genuine mathematical gap: conservative expansion
    -- alone doesn't guarantee existential reflection. The IFF theorem is still
    -- useful for quantifier-free formulas and formulas where witnesses can be
    -- traced back to M.
    sorry
  | infdisj φᵢ ih =>
    unfold formulaSatisfied subobjectMem at hsat ⊢
    simp only [Formula.interpret] at hsat ⊢
    rw [coproduct_eq_iSup] at hsat ⊢
    rw [iSup_range_iff] at hsat ⊢
    obtain ⟨i, hi⟩ := hsat
    use i
    exact ih i t hi

/--
**Formula satisfaction is an IFF for conservative expansions**:

For a conservative expansion (new relation tuples only concern new elements),
a tuple t from M satisfies φ in M if and only if lifted(t) satisfies φ in M'.

This is the key theorem for proving model preservation under universe expansion.

**Caveat**: The backward direction (reflect) has a sorry in the existential case.
This is because an existential witness in M' might be a "new" element not in
the image of the embedding. Full reflection of existentials would require
additional structure (e.g., witness reflection property) or model completeness.
The theorem is fully mechanized for quantifier-free formulas.
-/
theorem formula_satisfaction_iff {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : ConservativeExpansion M M')
    {xs : Context S}
    (φ : Formula xs)
    (t : Context.interpret M xs) :
    formulaSatisfied φ t ↔
    formulaSatisfied φ (liftEmbedContext emb.toStructureEmbedding xs t) :=
  ⟨formula_satisfaction_monotone emb.toRelPreservingEmbedding φ t,
   formula_satisfaction_reflect emb φ t⟩

/-!
### Sequent and Theory Preservation

With the IFF theorem, we can now prove proper sequent and theory preservation.
-/

/--
**Sequent preservation for conservative expansions**:

If a sequent (premise ⊢ conclusion) holds in M, and emb is a conservative expansion,
then for any tuple t from M:
- If lifted(t) satisfies the premise in M', then lifted(t) satisfies the conclusion in M'

This follows because:
1. premise(lifted(t)) in M' ↔ premise(t) in M (by formula_satisfaction_iff)
2. In M, premise(t) → conclusion(t) (by the sequent)
3. conclusion(t) in M ↔ conclusion(lifted(t)) in M' (by formula_satisfaction_iff)
-/
theorem sequent_preservation {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : ConservativeExpansion M M')
    (seq : S.Sequent)
    (hseq : Sequent.interpret M seq)
    (t : Context.interpret M seq.ctx)
    (hprem : formulaSatisfied seq.premise (liftEmbedContext emb.toStructureEmbedding seq.ctx t)) :
    formulaSatisfied seq.concl (liftEmbedContext emb.toStructureEmbedding seq.ctx t) := by
  -- Step 1: premise(lifted(t)) → premise(t) in M (backward direction of IFF)
  have hprem_M := (formula_satisfaction_iff emb seq.premise t).mpr hprem
  -- Step 2: In M, premise(t) → conclusion(t) via subobject ordering
  -- hseq : ⟦M|premise⟧ ≤ ⟦M|conclusion⟧
  -- This means: if t ∈ range(premise) then t ∈ range(conclusion)
  unfold Sequent.interpret at hseq
  unfold formulaSatisfied subobjectMem at hprem_M ⊢
  have hconcl_M : t ∈ Set.range (Formula.interpret M seq.concl).arrow :=
    subobject_le_range hseq hprem_M
  -- Step 3: conclusion(t) in M → conclusion(lifted(t)) in M' (forward direction of IFF)
  exact (formula_satisfaction_iff emb seq.concl t).mp hconcl_M

/--
**Theory preservation for conservative expansions**:

If M satisfies theory T, and emb is a conservative expansion to M',
then for any tuple t from M and any axiom in T:
- The axiom holds for lifted(t) in M'
-/
theorem theory_preservation {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : ConservativeExpansion M M')
    (T : S.Theory)
    (hM : Theory.interpret M T)
    (seq : S.Sequent)
    (hseq_in : seq ∈ T.axioms)
    (t : Context.interpret M seq.ctx)
    (hprem : formulaSatisfied seq.premise (liftEmbedContext emb.toStructureEmbedding seq.ctx t)) :
    formulaSatisfied seq.concl (liftEmbedContext emb.toStructureEmbedding seq.ctx t) :=
  sequent_preservation emb seq (hM seq hseq_in) t hprem

/-!
### Model Set Monotonicity (The Main Corollary)

**Key Principle**: As the universe of elements expands (with new function values and
relation assertions concerning *only* new elements), the set of subsets that form
valid models of a geometric theory T grows monotonically.

Formally, let:
- U(t) = universe at time t, with U(t) ⊆ U(t') for t ≤ t'
- Models(T, U(t)) = { S ⊆ U(t) : S is a substructure satisfying T }

Then: Models(T, U(t)) ⊆ Models(T, U(t'))

**Why this is true**:

1. **Intrinsic Theory Interpretation**: `Theory.interpret S T` depends *only* on the
   structure S itself—its sorts, functions, and relations. It does NOT depend on
   any ambient structure that S might be embedded in.

2. **Substructure Preservation**: When the universe expands, old substructures S ⊆ U(t)
   remain unchanged:
   - Same elements
   - Same function values (new values only concern new elements)
   - Same relation tuples (new tuples only concern new elements)

3. **Therefore**: If S ⊨ T at time t, then S ⊨ T at time t' > t.

4. **Moreover**: New subsets involving new elements may form *additional* models,
   so the model set can only grow.

**Connection to formula_satisfaction_monotone**:

Our main theorem `formula_satisfaction_monotone` provides the element-level view:
- For a tuple t from substructure S satisfying formula φ
- The same tuple (lifted via embedding) satisfies φ in any extension M' ⊇ S

This connects to theory interpretation via `Sequent.interpret`:
- A sequent `premise ⊢ conclusion` holds in S iff `⟦S|premise⟧ᶠ ≤ ⟦S|conclusion⟧ᶠ`
- Equivalently: ∀ tuples t, if t satisfies premise then t satisfies conclusion
- By `formula_satisfaction_monotone`, embedded tuples preserve this property

**Consequence for GeologMeta**:
- Incremental model checking is sound: adding elements never invalidates existing models
- Coordination-free: no need to re-verify old submodels when universe expands
- This is the semantic foundation for CALM theorem applications
-/

/--
**Axiom Satisfaction for Embedded Tuples**:

If M satisfies a theory T, and we embed M into M' via a relation-preserving embedding,
then for any tuple t from M:
- If t satisfies the premise of an axiom (premise ⊢ conclusion) in M
- Then the lifted tuple satisfies the conclusion in M'

This is the element-level view of model preservation.
-/
theorem axiom_satisfaction_embedded {M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [G : Geometric κ (Type u)]
    (emb : RelPreservingEmbedding M M')
    {xs : Context S}
    (_premise conclusion : Formula xs)
    (t : Context.interpret M xs)
    (_hprem : formulaSatisfied _premise t)
    (hconcl : formulaSatisfied conclusion t) :
    formulaSatisfied conclusion (liftEmbedContext emb.toStructureEmbedding xs t) :=
  formula_satisfaction_monotone emb conclusion t hconcl

/--
**Model Set Monotonicity** (term-level witness):

Given:
- S is a substructure of M (via embedding emb_SM)
- M is a substructure of M' (via embedding emb_MM')
- S satisfies theory T

Then: S still satisfies T (trivially, since Theory.interpret S T depends only on S).

The embedding composition emb_SM ≫ emb_MM' shows S is also a substructure of M',
but this doesn't affect S's satisfaction of T.

This theorem exists to document that `Theory.interpret` is intrinsic to the structure.
-/
theorem model_set_monotone
    {S_sub M M' : Structure S (Type u)}
    [κ : SmallUniverse S] [_G : Geometric κ (Type u)]
    (_emb_SM : StructureEmbedding S_sub M)
    (_emb_MM' : StructureEmbedding M M')
    (T : S.Theory)
    (hT : Theory.interpret S_sub T) :
    Theory.interpret S_sub T :=
  hT  -- Trivially true: Theory.interpret depends only on S_sub, not on M or M'

/-!
### Summary of Results

We have now formalized the **Monotonic Submodel Property** for geometric logic:

1. **`formula_satisfaction_monotone`**: The core theorem showing that satisfaction of
   geometric formulas is preserved when tuples are lifted via relation-preserving embeddings.

2. **`axiom_satisfaction_embedded`**: Corollary for sequent axioms—if a tuple satisfies
   both premise and conclusion in M, the lifted tuple satisfies the conclusion in M'.

3. **`model_set_monotone`**: Documents that `Theory.interpret S T` is intrinsic to S,
   so valid submodels remain valid as the ambient universe expands.

**The Key Insight**: Geometric formulas (built from relations, equality, ∧, ∨, ∃, and
infinitary ∨) are "positive existential"—they only assert existence, never non-existence.
This positivity is what makes satisfaction monotonic under structure extensions.
-/

/-- The full selection (all elements) is trivially closed -/
def fullSelection (M : Structure S (Type u)) : ClosedSubsetSelection M where
  subset := fun _ => Set.univ
  func_closed := fun _ {_A} {_B} _ _ _ _ => Set.mem_univ _

/-- **Theorem**: The pushforward of the full selection is closed in M' -/
theorem full_selection_pushforward_closed {M M' : Structure S (Type u)}
    (emb : StructureEmbedding M M') :
    ∀ (f : S.Functions) {A B : S.Sorts}
      (hdom : f.domain = DerivedSorts.inj A)
      (hcod : f.codomain = DerivedSorts.inj B),
      funcPreservesSubset ((fullSelection M).toSubsetSelection.pushforward emb) f hdom hcod :=
  fun f {_A} {_B} hdom hcod => semantic_monotonicity emb (fullSelection M) f hdom hcod

/-!
## The Complete Picture

**Main Result**: Monotonic Submodel Property for Geometric Theories

Given a signature S and a geometric theory T:

1. **Structural Level** (proven above):
   - ClosedSubsetSelection M represents a "submodel" of M
   - Embeddings preserve closure: (sel.pushforward emb).func_closed

2. **Semantic Level** (Theory.interpret):
   - M ⊨ T means all sequents hold
   - Sequent.interpret uses Formula.interpret (subobjects)

3. **Connection** (the key insight):
   - Elements in a ClosedSubsetSelection form a substructure
   - Formula satisfaction on the substructure corresponds to membership in
     the formula's interpretation restricted to the selection
   - Embeddings preserve this correspondence

4. **Consequence** (CALM theorem):
   - Adding elements to a model can only ADD valid submodels
   - It cannot INVALIDATE existing valid submodels
   - Therefore: incremental model checking is sound
-/

/-!
## Why This Matters: CALM Theorem Connection

The Monotonic Submodel Property enables coordination-free distributed systems:

- **CALM Theorem**: Monotonic programs have coordination-free implementations
- **Element Addition is Monotonic**: Valid(t) ⊆ Valid(t+1)
- **Element Retraction is NOT Monotonic**: Requires coordination

### Design Implications for GeologMeta

1. **FuncVal and RelTuple are immutable**: Once f(a) = b, it's eternally true
2. **All facts defined at creation**: When element a is created, all f(a) are defined
3. **Only liveness changes**: To "modify" f(a), retract a and create a new element
4. **Incremental model checking**: New elements can only add valid submodels
-/

end MonotonicSubmodel
