/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Basic
import ConstructorTheory.Possible
import ConstructorTheory.Composition
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Principles.CompositionPrinciple

/-!
# Category-Theoretic Structure of Constructor Theory

Formalizes the category-theoretic properties of tasks, following
Gogioso et al. (2024). Tasks form a symmetric monoidal category
under sequential and parallel composition.

The key insight from Gogioso et al. is that constructor-theoretic
tasks can be understood as morphisms in the category **Rel** (sets
and relations), with sequential composition as relational composition
and parallel composition as the Cartesian product.

## Key results

* Tasks form a category under sequential composition
* Parallel composition is functorial (preserves composition)
* Possible tasks form a sub-structure closed under composition
* Transpose is a contravariant involution (dagger structure)

## References

* S. Gogioso et al., "Constructor Theory as Process Theory",
  arXiv:2401.05364 (2024)
* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- ============================================================
-- Tasks as a category: identity and composition laws
-- ============================================================

-- Sequential composition has a left unit: identity ∘ t = t.
-- This is already proved as Task.sequential_identity_left.
-- Here we package the three category laws together.

-- The category laws for tasks (identity + associativity).
-- This shows tasks form a category under sequential composition.
structure TaskCategoryLaws (S : Type) where
  -- Left identity
  left_id : ∀ (t : Task S), (Task.identity t.output).sequential t = t
  -- Right identity
  right_id : ∀ (t : Task S), t.sequential (Task.identity t.input) = t
  -- Associativity
  assoc : ∀ (t₁ t₂ t₃ : Task S),
    t₃.sequential (t₂.sequential t₁) = (t₃.sequential t₂).sequential t₁

-- Tasks always satisfy the category laws.
def taskCategoryLaws (S : Type) : TaskCategoryLaws S where
  left_id := Task.sequential_identity_left
  right_id := Task.sequential_identity_right
  assoc := Task.sequential_assoc

-- ============================================================
-- Dagger structure: transpose is a contravariant involution
-- ============================================================

-- The dagger (transpose) satisfies the involution law.
theorem transpose_involution {S : Type} (t : Task S) : t†† = t :=
  Task.transpose_transpose t

-- The dagger is contravariant on sequential composition:
-- (t₂ ∘ t₁)† = t₁† ∘ t₂†
-- Already proved as Task.sequential_transpose.

-- The dagger preserves identity: (id_a)† = id_a.
-- Already proved as Task.identity_transpose.

-- Package dagger laws together.
structure DaggerLaws (S : Type) where
  involution : ∀ (t : Task S), t†† = t
  contravariant : ∀ (t₁ t₂ : Task S), (t₂.sequential t₁)† = t₁†.sequential t₂†
  preserves_identity : ∀ (a : Attribute S), (Task.identity a)† = Task.identity a

-- Tasks always satisfy the dagger laws.
def taskDaggerLaws (S : Type) : DaggerLaws S where
  involution := Task.transpose_transpose
  contravariant := Task.sequential_transpose
  preserves_identity := Task.identity_transpose

-- ============================================================
-- Symmetric monoidal structure: parallel composition
-- ============================================================

-- Parallel composition distributes over sequential composition
-- (when the types match). This is the interchange law.
-- (t₂ ⊗ t₄) ∘ (t₁ ⊗ t₃) is related to (t₂ ∘ t₁) ⊗ (t₄ ∘ t₃)
-- at the level of input/output attributes.
theorem parallel_sequential_interchange {S₁ S₂ : Type}
    (t₁ t₂ : Task S₁) (t₃ t₄ : Task S₂) :
    ((t₂ ⊗ t₄).sequential (t₁ ⊗ t₃)).input =
      (t₂.sequential t₁ ⊗ t₄.sequential t₃).input := by
  simp [Task.sequential, Task.parallel]

-- The output also matches under the interchange law.
theorem parallel_sequential_interchange_output {S₁ S₂ : Type}
    (t₁ t₂ : Task S₁) (t₃ t₄ : Task S₂) :
    ((t₂ ⊗ t₄).sequential (t₁ ⊗ t₃)).output =
      (t₂.sequential t₁ ⊗ t₄.sequential t₃).output := by
  simp [Task.sequential, Task.parallel]

-- The interchange law holds at the task level.
theorem parallel_sequential_interchange_eq {S₁ S₂ : Type}
    (t₁ t₂ : Task S₁) (t₃ t₄ : Task S₂) :
    (t₂ ⊗ t₄).sequential (t₁ ⊗ t₃) =
      t₂.sequential t₁ ⊗ t₄.sequential t₃ := by
  simp [Task.sequential, Task.parallel]

-- ============================================================
-- Possible tasks form a sub-category
-- ============================================================

-- In a ComposableUniverse, possible tasks are closed under
-- sequential composition (Proposition 3.4 of Gogioso et al.).
-- Already proved as sequential_of_possible.

-- In a ComposableUniverse with locality, possible tasks are closed
-- under parallel composition with spectators.
-- Already proved as locality_spectator.

-- Possible identity tasks always exist (closure of identities).
-- Already proved as identity_task_possible.

-- The subcategory of possible tasks inherits the category structure.
structure PossibleTaskSubcategory (S : Type) [ComposableUniverse S] where
  -- Identity closure: identity tasks are always possible
  identity_closed : ∀ (a : Attribute S), Possible (Task.identity a)
  -- Composition closure: sequential composition of possible tasks is possible
  composition_closed : ∀ (t₁ t₂ : Task S),
    Possible t₁ → Possible t₂ → Possible (t₂.sequential t₁)

-- Every ComposableUniverse has a subcategory of possible tasks.
def possibleSubcategory (S : Type) [ComposableUniverse S] :
    PossibleTaskSubcategory S where
  identity_closed := identity_task_possible
  composition_closed := fun _t₁ _t₂ h₁ h₂ => sequential_of_possible h₁ h₂

-- ============================================================
-- Reversible tasks form a sub-dagger-category
-- ============================================================

-- In a ComposableUniverse, reversible tasks are closed under
-- sequential composition.
-- Already proved as sequential_preserves_reversibility.

-- Reversible tasks are closed under transpose.
-- Already proved as Reversible.transpose.

-- Identity tasks are reversible in a ConstructorUniverse.
theorem identity_reversible {S : Type} [ConstructorUniverse S]
    (a : Attribute S) : Reversible (Task.identity a) := by
  constructor
  · exact identity_task_possible a
  · simp [Task.identity_transpose]
    exact identity_task_possible a

-- The sub-dagger-category of reversible tasks.
structure ReversibleSubcategory (S : Type) [ComposableUniverse S] where
  -- Identity closure
  identity_closed : ∀ (a : Attribute S), Reversible (Task.identity a)
  -- Composition closure
  composition_closed : ∀ (t₁ t₂ : Task S),
    Reversible t₁ → Reversible t₂ → Reversible (t₂.sequential t₁)
  -- Dagger closure
  dagger_closed : ∀ (t : Task S), Reversible t → Reversible t†

-- Every ComposableUniverse has a sub-dagger-category of reversible tasks.
def reversibleSubcategory (S : Type) [ComposableUniverse S] :
    ReversibleSubcategory S where
  identity_closed := identity_reversible
  composition_closed := fun _t₁ _t₂ h₁ h₂ =>
    sequential_preserves_reversibility h₁ h₂
  dagger_closed := fun _t h => h.transpose

end ConstructorTheory
