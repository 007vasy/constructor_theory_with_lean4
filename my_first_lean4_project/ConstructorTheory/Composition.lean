/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Basic

/-!
# Composition of Tasks

This file defines parallel composition of constructor-theoretic tasks.

*Parallel composition* `T₁ ⊗ T₂` applies tasks `T₁` and `T₂` simultaneously
to independent substrates. If `T₁ = {a₁ → b₁}` on `S₁` and `T₂ = {a₂ → b₂}`
on `S₂`, then `T₁ ⊗ T₂ = {(a₁, a₂) → (b₁, b₂)}` on `S₁ × S₂`.

## References

* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- An attribute on a product substrate: both component attributes hold.
def Attribute.prod {S₁ S₂ : Type} (a₁ : Attribute S₁) (a₂ : Attribute S₂) :
    Attribute (S₁ × S₂) :=
  fun p => a₁ p.1 ∧ a₂ p.2

-- Parallel composition of tasks on independent substrates.
-- Given T₁ on S₁ and T₂ on S₂, the parallel composition T₁ ⊗ T₂
-- is a task on S₁ × S₂.
def Task.parallel {S₁ S₂ : Type} (t₁ : Task S₁) (t₂ : Task S₂) :
    Task (S₁ × S₂) where
  input := Attribute.prod t₁.input t₂.input
  output := Attribute.prod t₁.output t₂.output

-- Notation for parallel composition.
infixl:70 " ⊗ " => Task.parallel

-- The transpose of a parallel composition is the parallel composition
-- of the transposes.
@[simp]
theorem Task.parallel_transpose {S₁ S₂ : Type} (t₁ : Task S₁) (t₂ : Task S₂) :
    (t₁ ⊗ t₂)† = t₁† ⊗ t₂† := by
  simp [Task.parallel, Task.transpose]

-- Parallel composition of identity tasks is the identity on the product.
theorem Task.parallel_identity {S₁ S₂ : Type}
    (a₁ : Attribute S₁) (a₂ : Attribute S₂) :
    Task.identity a₁ ⊗ Task.identity a₂ = Task.identity (Attribute.prod a₁ a₂) := by
  simp [Task.parallel, Task.identity, Attribute.prod]

-- The spectator task: maps a single attribute to itself (identity on one attr).
-- Used in the locality principle: attaching a spectator should not affect
-- the possibility of the original task.
def Task.spectator {S : Type} (a : Attribute S) : Task S :=
  Task.identity a

-- Parallel composition with a spectator on the right.
def Task.withSpectator {S₁ S₂ : Type} (t : Task S₁) (a : Attribute S₂) :
    Task (S₁ × S₂) :=
  t ⊗ Task.spectator a

-- Parallel composition with a spectator preserves transpose structure.
theorem Task.withSpectator_transpose {S₁ S₂ : Type}
    (t : Task S₁) (a : Attribute S₂) :
    (t.withSpectator a)† = t†.withSpectator a := by
  simp [Task.withSpectator, Task.spectator]

end ConstructorTheory
