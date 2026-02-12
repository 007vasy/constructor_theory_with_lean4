/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/

/-!
# Constructor Theory: Core Definitions

This file defines the foundational types of constructor theory following
Deutsch (2013) and Deutsch & Marletto (2014).

## Main definitions

* `Attribute` - A predicate on states of a substrate
* `Task` - An input-output pair of attributes
* `CompositeTask` - A nonempty list of tasks
* `Variable` - A list of mutually disjoint attributes (an observable)

## References

* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- An `Attribute` on a state type `S` is a predicate on states.
-- It holds for all states in which the substrate "has" that attribute.
def Attribute (S : Type) := S → Prop

-- Two attributes are `Disjoint` if no state can satisfy both simultaneously.
def Attribute.Disjoint {S : Type} (a b : Attribute S) : Prop :=
  ∀ s : S, ¬(a s ∧ b s)

-- `Attribute.Disjoint` is symmetric.
theorem Attribute.Disjoint.symm {S : Type} {a b : Attribute S}
    (h : Attribute.Disjoint a b) : Attribute.Disjoint b a :=
  fun s ⟨hb, ha⟩ => h s ⟨ha, hb⟩

-- A `Task` specifies a single input-output pair of attributes.
-- It represents "cause the input attribute to become the output attribute".
-- Following Deutsch (2013), the simplest task is {a → b}.
structure Task (S : Type) where
  input : Attribute S
  output : Attribute S

-- A `CompositeTask` bundles multiple input-output pairs.
-- Following Deutsch (2013), T = {a₁ → b₁, a₂ → b₂, ...}.
structure CompositeTask (S : Type) where
  tasks : List (Task S)
  nonempty : tasks ≠ []

-- Create a composite task from a single task.
def CompositeTask.singleton {S : Type} (t : Task S) : CompositeTask S where
  tasks := [t]
  nonempty := List.cons_ne_nil _ _

-- The `transpose` of a task swaps input and output.
-- If T = {a → b}, then T† = {b → a}.
-- Fundamental to the notion of reversibility in constructor theory.
def Task.transpose {S : Type} (t : Task S) : Task S where
  input := t.output
  output := t.input

-- Notation: t† denotes the transpose of task t.
postfix:max "†" => Task.transpose

-- The transpose of a transpose is the original task.
@[simp]
theorem Task.transpose_transpose {S : Type} (t : Task S) :
    t†† = t := by
  simp [Task.transpose]

-- The transpose of a composite task transposes each pair.
def CompositeTask.transpose {S : Type} (ct : CompositeTask S) : CompositeTask S where
  tasks := ct.tasks.map Task.transpose
  nonempty := by
    intro h
    have : ct.tasks = [] := by
      cases htl : ct.tasks with
      | nil => rfl
      | cons hd tl => simp [htl, List.map] at h
    exact ct.nonempty this

-- The input attributes of a composite task.
def CompositeTask.inputs {S : Type} (ct : CompositeTask S) : List (Attribute S) :=
  ct.tasks.map Task.input

-- The output attributes of a composite task.
def CompositeTask.outputs {S : Type} (ct : CompositeTask S) : List (Attribute S) :=
  ct.tasks.map Task.output

-- A `Variable` (or observable) is a collection of mutually disjoint attributes.
-- Each element represents a distinguishable macro-state.
-- Must contain at least two attributes (Deutsch & Marletto).
structure Variable (S : Type) where
  attrs : List (Attribute S)
  nontrivial : attrs.length ≥ 2
  pairwise_disjoint : ∀ i j : Fin attrs.length,
    i ≠ j → Attribute.Disjoint (attrs.get i) (attrs.get j)

-- The identity task on an attribute maps it to itself.
def Task.identity {S : Type} (a : Attribute S) : Task S where
  input := a
  output := a

-- The identity task is its own transpose.
@[simp]
theorem Task.identity_transpose {S : Type} (a : Attribute S) :
    (Task.identity a)† = Task.identity a := by
  simp [Task.identity, Task.transpose]

-- Sequential composition: do t₁ then t₂.
-- The output of t₁ feeds into the input of t₂.
def Task.sequential {S : Type} (t₂ t₁ : Task S) : Task S where
  input := t₁.input
  output := t₂.output

-- Sequential composition with identity (left) is trivial.
@[simp]
theorem Task.sequential_identity_left {S : Type} (t : Task S) :
    (Task.identity t.output).sequential t = t := by
  simp [Task.sequential, Task.identity]

-- Sequential composition with identity (right) is trivial.
@[simp]
theorem Task.sequential_identity_right {S : Type} (t : Task S) :
    t.sequential (Task.identity t.input) = t := by
  simp [Task.sequential, Task.identity]

-- Sequential composition is associative.
theorem Task.sequential_assoc {S : Type} (t₁ t₂ t₃ : Task S) :
    t₃.sequential (t₂.sequential t₁) = (t₃.sequential t₂).sequential t₁ := by
  simp [Task.sequential]

-- The transpose of a sequential composition reverses the order.
theorem Task.sequential_transpose {S : Type} (t₁ t₂ : Task S) :
    (t₂.sequential t₁)† = t₁†.sequential t₂† := by
  simp [Task.sequential, Task.transpose]

end ConstructorTheory
