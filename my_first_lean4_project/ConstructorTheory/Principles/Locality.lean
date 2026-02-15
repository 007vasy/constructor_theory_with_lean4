/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Principles.Basic

/-!
# Principle II: Locality

Extended results about the locality principle.

The locality principle states that if a task T is possible on substrate S₁,
then T performed alongside a spectator (doing nothing) on any other
substrate S₂ is also possible. Formally: if T is possible on S₁,
then T ⊗ id(a₂) is possible on S₁ × S₂ for any attribute a₂ of S₂.

This captures a deep physical principle: distant substrates cannot
retroactively prevent a local task from being performed.

## Main results

* `locality_spectator` - Direct application of the locality axiom
* `locality_preserves_reversibility` - Locality preserves reversibility

## References

* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- Direct statement of the locality principle: a possible task
-- remains possible when composed with a spectator.
theorem locality_spectator {S₁ : Type} [LocalUniverse S₁]
    {S₂ : Type} [TaskPossibility (S₁ × S₂)]
    {t : Task S₁} (ht : Possible t) (a₂ : Attribute S₂) :
    Possible (t.withSpectator a₂) :=
  LocalUniverse.locality S₂ t a₂ ht

-- Locality preserves reversibility: if a task is reversible on S₁,
-- then its extension with a spectator is also reversible on S₁ × S₂
-- (provided the product universe also satisfies locality for transposes).
theorem locality_preserves_reversibility {S₁ : Type} [LocalUniverse S₁]
    {S₂ : Type} [TaskPossibility (S₁ × S₂)]
    {t : Task S₁} (ht : Reversible t) (a₂ : Attribute S₂)
    (h_transpose : Possible t† → Possible (t†.withSpectator a₂)) :
    Reversible (t.withSpectator a₂) := by
  constructor
  · exact locality_spectator ht.1 a₂
  · rw [Task.withSpectator_transpose]
    exact h_transpose ht.2

end ConstructorTheory
