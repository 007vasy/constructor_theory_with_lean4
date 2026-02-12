/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Possible
import ConstructorTheory.Composition

/-!
# Principle I: Counterfactual Foundation

Constructor theory's Principle I states that all fundamental laws of physics
are expressible entirely in terms of statements about which tasks are possible,
which are impossible, and why.

A `ConstructorUniverse` formalizes this by bundling a substrate with axioms
constraining the `Possible` predicate.

## References

* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- A `ConstructorUniverse` formalizes Principle I: all physical laws
-- are expressed solely via the `Possible` predicate on tasks.
-- The identity axiom ensures that "doing nothing" is always possible.
class ConstructorUniverse (S : Type) extends TaskPossibility S where
  -- The identity task (doing nothing) on any attribute is possible.
  identity_possible : ∀ (a : Attribute S), Possible (Task.identity a)

-- In a ConstructorUniverse, the identity task is always possible.
theorem identity_task_possible {S : Type} [ConstructorUniverse S]
    (a : Attribute S) : Possible (Task.identity a) :=
  ConstructorUniverse.identity_possible a

-- Principle VII (Composition): Possible tasks are closed under
-- parallel and sequential composition. This is a strengthening
-- of the basic ConstructorUniverse.
class ComposableUniverse (S : Type) extends ConstructorUniverse S where
  -- Sequential composition preserves possibility.
  sequential_possible : ∀ (t₁ t₂ : Task S),
    Possible t₁ → Possible t₂ → Possible (t₂.sequential t₁)

-- If sequential composition preserves possibility, then
-- the sequential composition of two possible tasks is possible.
theorem sequential_of_possible {S : Type} [ComposableUniverse S]
    {t₁ t₂ : Task S} (h₁ : Possible t₁) (h₂ : Possible t₂) :
    Possible (t₂.sequential t₁) :=
  ComposableUniverse.sequential_possible t₁ t₂ h₁ h₂

-- Principle II (Locality): A `LocalUniverse` extends `ConstructorUniverse`
-- with the axiom that possible tasks remain possible in the presence
-- of spectator substrates.
-- If T is possible on S₁, then T ⊗ spectator(a₂) is possible on S₁ × S₂
-- for any attribute a₂ of any substrate S₂.
class LocalUniverse (S₁ : Type) extends ConstructorUniverse S₁ where
  -- Locality: spectators don't affect possibility.
  locality : ∀ (S₂ : Type) [TaskPossibility (S₁ × S₂)]
    (t : Task S₁) (a₂ : Attribute S₂),
    Possible t → Possible (t.withSpectator a₂)

-- The contrapositive of composition: if a parallel task is impossible,
-- then at least one component must be impossible.
-- (This requires an additional axiom about parallel composition
-- preserving possibility, stated here as a hypothesis.)
theorem parallel_impossible_of {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂] [TaskPossibility (S₁ × S₂)]
    {t₁ : Task S₁} {t₂ : Task S₂}
    (h_comp : Possible t₁ → Possible t₂ → Possible (t₁ ⊗ t₂))
    (h_imp : Impossible (t₁ ⊗ t₂)) :
    Impossible t₁ ∨ Impossible t₂ :=
  Classical.byContradiction fun h =>
    have h₁ : Possible t₁ := Classical.byContradiction fun h₁ => h (Or.inl h₁)
    have h₂ : Possible t₂ := Classical.byContradiction fun h₂ => h (Or.inr h₂)
    h_imp (h_comp h₁ h₂)

end ConstructorTheory
