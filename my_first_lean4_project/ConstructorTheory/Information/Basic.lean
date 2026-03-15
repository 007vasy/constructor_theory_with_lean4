/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Basic
import ConstructorTheory.Possible
import ConstructorTheory.Composition

/-!
# Constructor Theory of Information: Variables

Defines computation variables and information variables following
Deutsch & Marletto (2014).

A *computation variable* is a variable where every permutation of its
attributes can be performed by some constructor.

An *information variable* is a computation variable that is also *clonable*:
there exists a "blank" attribute such that the cloning task is possible.

## Main definitions

* `IsComputationVariable` - All swaps of attributes are possible
* `IsInformationVariable` - Clonable computation variable
* `IsInformationMedium` - A substrate with at least one information variable
* `IsSuperinformationMedium` - Has two info variables whose union is not info

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- A variable is a `ComputationVariable` if for every pair of attributes
-- in the variable, the swap task (mapping one to the other) is possible.
-- This is equivalent to saying all permutations are possible, since
-- any permutation can be decomposed into transpositions.
def IsComputationVariable {S : Type} [TaskPossibility S] (v : Variable S) : Prop :=
  ∀ i j : Fin v.attrs.length,
    Possible { input := v.attrs.get i, output := v.attrs.get j : Task S }

-- The cloning task for a single attribute: given a "blank" attribute b₀,
-- map (a, b₀) → (a, a) on the product substrate S × S.
def cloneTaskSingle {S : Type} (a blank : Attribute S) : Task (S × S) where
  input := Attribute.prod a blank
  output := Attribute.prod a a

-- A computation variable is an `InformationVariable` if it is clonable:
-- there exists a "blank" attribute such that for every attribute a in the
-- variable, the task (a, blank) → (a, a) is possible.
def IsInformationVariable {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  IsComputationVariable v ∧
  ∃ blank : Attribute S,
    ∀ i : Fin v.attrs.length,
      Possible (cloneTaskSingle (v.attrs.get i) blank)

-- An information variable is a computation variable.
theorem IsInformationVariable.toComputationVariable
    {S : Type} [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsInformationVariable v) :
    IsComputationVariable v :=
  h.1

-- A substrate is an `InformationMedium` if it has at least one
-- information variable.
def IsInformationMedium (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] : Prop :=
  ∃ v : Variable S, IsInformationVariable v

-- A substrate is a `SuperinformationMedium` if it has two information
-- variables whose union is NOT an information variable.
-- Quantum systems are superinformation media: the union of two
-- complementary observables (e.g., spin-x and spin-z eigenstates)
-- cannot be cloned (no-cloning theorem).
def IsSuperinformationMedium (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] : Prop :=
  IsInformationMedium S ∧
  ∃ (v₁ v₂ : Variable S),
    IsInformationVariable v₁ ∧
    IsInformationVariable v₂ ∧
    ∀ (v_union : Variable S),
      (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
      (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
      ¬ IsInformationVariable v_union

-- A superinformation medium is an information medium.
theorem IsSuperinformationMedium.toInformationMedium
    {S : Type} [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsSuperinformationMedium S) : IsInformationMedium S :=
  h.1

end ConstructorTheory
