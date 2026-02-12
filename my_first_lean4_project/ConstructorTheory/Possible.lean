/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Basic

/-!
# Possible and Impossible Tasks

A task is *possible* if there exists a constructor that can perform it to
arbitrarily high accuracy, retaining the ability to do so again. A task is
*impossible* if there is a law of physics that forbids it.

These are the primitive counterfactual predicates of constructor theory,
replacing dynamical laws as the fundamental mode of physical explanation.

## References

* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- `Possible` is modeled as an axiomatically given predicate on tasks.
-- In constructor theory, this is the primitive notion from which all
-- physics is derived. We use a typeclass so different physical theories
-- can provide different `Possible` predicates.
class TaskPossibility (S : Type) where
  possible : Task S → Prop

-- A task is `Possible` if the `TaskPossibility` instance says so.
def Possible {S : Type} [TaskPossibility S] (t : Task S) : Prop :=
  TaskPossibility.possible t

-- A task is `Impossible` if it is not possible.
def Impossible {S : Type} [TaskPossibility S] (t : Task S) : Prop :=
  ¬ Possible t

-- Possible and Impossible are complementary.
theorem impossible_iff_not_possible {S : Type} [TaskPossibility S] {t : Task S} :
    Impossible t ↔ ¬ Possible t :=
  Iff.rfl

-- Every task is either possible or impossible (classical logic).
theorem possible_or_impossible {S : Type} [TaskPossibility S] (t : Task S) :
    Possible t ∨ Impossible t := by
  exact Classical.em (Possible t)

-- A task is `Reversible` if both it and its transpose are possible.
-- This captures the constructor-theoretic notion of thermodynamic
-- reversibility.
def Reversible {S : Type} [TaskPossibility S] (t : Task S) : Prop :=
  Possible t ∧ Possible t†

-- If a task is reversible, so is its transpose.
theorem Reversible.transpose {S : Type} [TaskPossibility S] {t : Task S}
    (h : Reversible t) : Reversible t† := by
  constructor
  · exact h.2
  · simp [Task.transpose_transpose]
    exact h.1

-- A composite task is `AllPossible` if every component task is possible.
def CompositeTask.AllPossible {S : Type} [TaskPossibility S]
    (ct : CompositeTask S) : Prop :=
  ∀ t ∈ ct.tasks, Possible t

-- A composite task is `AllReversible` if every component is reversible.
def CompositeTask.AllReversible {S : Type} [TaskPossibility S]
    (ct : CompositeTask S) : Prop :=
  ∀ t ∈ ct.tasks, Reversible t

end ConstructorTheory
