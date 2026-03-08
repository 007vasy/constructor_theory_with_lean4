/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Basic
import ConstructorTheory.Possible
import ConstructorTheory.Composition
import ConstructorTheory.Principles.Basic

/-!
# Constructor as Catalyst: Process-Theoretic Foundations

Formalizes the constructor-as-catalyst paradigm from Gogioso et al. (2024).
A constructor is a substrate that enables a task while retaining the
ability to do so again — formally, a catalyst in the process-theoretic sense.

The key definition: a task T on substrate S is *possible* if there exists
a constructor substrate C with an attribute P such that the composite task
T ⊗ id_P on S × C is achievable and the constructor remains in attribute P.

## Key concepts

* *Constructor*: A catalyst substrate that enables a task
* *Retentive task*: A task that preserves the constructor's attribute
* *Constructor reliability*: The constructor can operate repeatedly
* *Catalyst composition*: Composing constructors for composite tasks

## References

* S. Gogioso et al., "Constructor Theory as Process Theory",
  arXiv:2401.05364 (2024)
* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- ============================================================
-- Constructor as catalyst
-- ============================================================

-- A `Constructor` for task t is a substrate C with a catalyst
-- attribute that enables t while being preserved.
structure Constructor (S C : Type)
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)] where
  -- The task being performed
  task : Task S
  -- The constructor's ready attribute
  ready : Attribute C
  -- The composite task: (task.input, ready) → (task.output, ready)
  -- The constructor remains in its ready state after the task
  composite_possible : Possible
    { input := Attribute.prod task.input ready,
      output := Attribute.prod task.output ready : Task (S × C) }

-- A constructor-enabled task is possible (by definition).
theorem Constructor.task_achievable {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (con : Constructor S C) :
    Possible { input := Attribute.prod con.task.input con.ready,
               output := Attribute.prod con.task.output con.ready :
               Task (S × C) } :=
  con.composite_possible

-- ============================================================
-- Constructor reliability
-- ============================================================

-- A constructor is `Reliable` if it can perform the task arbitrarily
-- many times (formalized as: after performing the task, the constructor
-- is still in its ready state, so it can go again).
-- This is already captured by the Constructor definition (the ready
-- attribute is preserved), but we make it explicit.
def Constructor.isReliable {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (con : Constructor S C) : Prop :=
  -- The constructor preserves its ready state
  Possible { input := Attribute.prod con.task.input con.ready,
             output := Attribute.prod con.task.output con.ready : Task (S × C) }

-- Every constructor is reliable (by definition).
theorem Constructor.reliable {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (con : Constructor S C) : con.isReliable :=
  con.composite_possible

-- ============================================================
-- Retentive tasks
-- ============================================================

-- A task on a product substrate is `Retentive` for an attribute
-- if the attribute is preserved in the second component.
def IsRetentive {S C : Type}
    (t : Task (S × C)) (a : Attribute C) : Prop :=
  ∀ (_s₁ _s₂ : S) (c : C),
    t.input (_s₁, c) → a c →
    ∀ (_s₂' : S) (c' : C),
      t.output (_s₂', c') → a c'

-- ============================================================
-- Impossible tasks have no constructor
-- ============================================================

-- If a task has no constructor in any substrate, it is impossible
-- (in the constructor-theoretic sense). This is the contrapositive
-- of the constructor definition.
-- Note: this is a meta-statement about the relationship between
-- constructors and impossibility.
theorem no_constructor_implies_structure {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (t : Task S) (ready : Attribute C)
    (h : Impossible { input := Attribute.prod t.input ready,
                      output := Attribute.prod t.output ready : Task (S × C) }) :
    ¬ (∃ (_ : Constructor S C), True) ∨
    ∀ (con : Constructor S C), con.task ≠ t ∨ con.ready ≠ ready := by
  right
  intro con
  by_cases htask : con.task = t
  · by_cases hready : con.ready = ready
    · exfalso
      subst htask; subst hready
      exact h con.composite_possible
    · exact Or.inr hready
  · exact Or.inl htask

-- ============================================================
-- Identity constructor
-- ============================================================

-- The identity task always has a trivial constructor (in a
-- ConstructorUniverse): the substrate itself serves as the constructor.
def identityConstructor {S C : Type}
    [TaskPossibility S] [ConstructorUniverse C]
    [TaskPossibility (S × C)]
    (a_s : Attribute S) (a_c : Attribute C)
    (h : Possible { input := Attribute.prod a_s a_c,
                    output := Attribute.prod a_s a_c : Task (S × C) }) :
    Constructor S C where
  task := Task.identity a_s
  ready := a_c
  composite_possible := h

-- ============================================================
-- Constructor for transpose
-- ============================================================

-- If task t has a constructor with a given ready attribute, and
-- the transpose composite is also possible, then t† also has a
-- constructor with the same ready attribute.
def transposeConstructor {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (con : Constructor S C)
    (h_rev : Possible { input := Attribute.prod con.task.output con.ready,
                        output := Attribute.prod con.task.input con.ready :
                        Task (S × C) }) :
    Constructor S C where
  task := con.task†
  ready := con.ready
  composite_possible := h_rev

-- ============================================================
-- Approximation and constructor theory
-- ============================================================

-- In constructor theory, "possible" means "to arbitrarily high
-- accuracy." This is captured by the constructor retaining its
-- ability. We formalize this as: if a constructor exists, it can
-- perform the task without degradation (the catalyst is not consumed).
-- This is already implicit in the Constructor definition, but we
-- state it explicitly.
theorem constructor_not_consumed {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (con : Constructor S C) :
    -- After performing the task, the constructor is still ready
    -- (its ready attribute is preserved in the output)
    ∃ (task_out : Attribute S),
      task_out = con.task.output ∧
      Possible { input := Attribute.prod con.task.input con.ready,
                 output := Attribute.prod task_out con.ready : Task (S × C) } :=
  ⟨con.task.output, rfl, con.composite_possible⟩

end ConstructorTheory
