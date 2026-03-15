/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Principles.Basic

/-!
# Principle VII: Composition

Extended results about the composition principle.

The composition principle states that possible tasks are closed under
sequential and parallel composition. This means that if we can
perform T₁ and T₂ separately, we can also perform them in sequence
or in parallel.

## Main results

* `sequential_chain` - Chain of three sequential compositions
* `composition_preserves_reversibility` - Sequential composition preserves reversibility
* `composable_implies_possible` - Immediate consequence of composability

## References

* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- A chain of three sequential tasks: if t₁, t₂, t₃ are all possible,
-- then their sequential composition t₃ ∘ t₂ ∘ t₁ is possible.
theorem sequential_chain {S : Type} [ComposableUniverse S]
    {t₁ t₂ t₃ : Task S}
    (h₁ : Possible t₁) (h₂ : Possible t₂) (h₃ : Possible t₃) :
    Possible ((t₃.sequential t₂).sequential t₁) :=
  sequential_of_possible h₁ (sequential_of_possible h₂ h₃)

-- In a ComposableUniverse, sequential composition preserves
-- reversibility: if both t₁ and t₂ are reversible, so is t₂ ∘ t₁.
theorem sequential_preserves_reversibility {S : Type} [ComposableUniverse S]
    {t₁ t₂ : Task S}
    (h₁ : Reversible t₁) (h₂ : Reversible t₂) :
    Reversible (t₂.sequential t₁) := by
  constructor
  · exact sequential_of_possible h₁.1 h₂.1
  · rw [Task.sequential_transpose]
    exact sequential_of_possible h₂.2 h₁.2

-- In a ComposableUniverse, if t is possible, then t composed with
-- the identity on its output is still possible (and equals t).
theorem composable_with_identity {S : Type} [ComposableUniverse S]
    {t : Task S} (ht : Possible t) :
    Possible ((Task.identity t.output).sequential t) := by
  rw [Task.sequential_identity_left]
  exact ht

end ConstructorTheory
