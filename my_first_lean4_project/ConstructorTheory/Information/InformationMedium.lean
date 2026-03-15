/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Information.Basic
import ConstructorTheory.Principles.Basic

/-!
# Information Media: Extended Properties

Additional theorems about information and superinformation media.

A key result of constructor theory of information is that classical and
quantum substrates differ in their information-theoretic structure:
- Classical systems: all information variables can be unified into a
  single information variable.
- Quantum systems: there exist pairs of information variables whose
  union cannot be an information variable (superinformation).

## Main results

* `computation_variable_swap` - Any pair swap in a computation variable is possible
* `IsInformationVariable.clone_possible` - Cloning is possible for info variables
* `superinfo_implies_incompatible_observables` - Superinformation media have
  incompatible observables

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- In a computation variable, any swap between two attributes is possible.
-- This is a direct consequence of the definition.
theorem computation_variable_swap {S : Type} [TaskPossibility S]
    {v : Variable S} (hv : IsComputationVariable v)
    (i j : Fin v.attrs.length) :
    Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } :=
  hv i j

-- A computation variable allows composing permutations: if i→j and j→k are
-- both possible, and we have a ComposableUniverse, then i→k is possible
-- (though the composed task may have different intermediate attributes).
theorem computation_variable_transitive {S : Type} [ComposableUniverse S]
    {v : Variable S} (hv : IsComputationVariable v)
    (i j k : Fin v.attrs.length) :
    Possible ({ output := v.attrs.get k, input := v.attrs.get j : Task S}.sequential
      { input := v.attrs.get i, output := v.attrs.get j : Task S }) :=
  sequential_of_possible (hv i j) (hv j k)

-- An information variable has a clone task for each of its attributes.
theorem IsInformationVariable.clone_possible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsInformationVariable v)
    (i : Fin v.attrs.length) :
    ∃ blank : Attribute S, Possible (cloneTaskSingle (v.attrs.get i) blank) :=
  let ⟨blank, hclone⟩ := hv.2
  ⟨blank, hclone i⟩

-- The identity task on each attribute of a computation variable is possible
-- (in a ConstructorUniverse).
theorem computation_variable_identity {S : Type} [ConstructorUniverse S]
    {v : Variable S} (_hv : IsComputationVariable v)
    (i : Fin v.attrs.length) :
    Possible (Task.identity (v.attrs.get i)) :=
  identity_task_possible (v.attrs.get i)

-- If a substrate is a superinformation medium, there exist two information
-- variables with incompatible attributes (i.e., their union cannot form
-- an information variable). This is the formal expression of quantum
-- complementarity in constructor-theoretic terms.
theorem superinfo_implies_incompatible_observables {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsSuperinformationMedium S) :
    ∃ (v₁ v₂ : Variable S),
      IsInformationVariable v₁ ∧
      IsInformationVariable v₂ ∧
      ∀ (v_union : Variable S),
        (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
        (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
        ¬ IsInformationVariable v_union :=
  h.2

end ConstructorTheory
