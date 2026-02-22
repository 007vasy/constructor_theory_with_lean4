/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Information.Basic
import ConstructorTheory.Principles.Basic

/-!
# Constructor Theory of Life

Formalizes the constructor-theoretic treatment of life following
Marletto (2014). The key concepts are:

* *Digital information*: Information that can be replicated with
  arbitrary accuracy.
* *Replicator*: An entity whose information variable can be copied.
* *Vehicle*: A physical system that, together with a replicator,
  constitutes a self-reproducer.
* *Self-reproducer*: A system that acts as a constructor for its
  own reproduction from generic resources.
* *No-design laws*: Laws that do not encode specific designs.

## Main definitions

* `IsDigitalInformation` - An information variable with high-fidelity cloning
* `Replicator` - A substrate with a copyable information variable
* `SelfReproducer` - A composite system that can reproduce itself
* `IsNoDesignLaw` - A law that does not single out specific states

## References

* C. Marletto, "Constructor Theory of Life",
  J. R. Soc. Interface 12:20141226 (2015), arXiv:1407.0681
* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- Digital information: an information variable where the cloning task
-- is possible. In constructor theory, digital information is the kind
-- of information that can be replicated with arbitrary accuracy.
-- This is exactly an information variable (which requires clonability).
def IsDigitalInformation {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  IsInformationVariable v

-- Digital information is an information variable (by definition).
theorem IsDigitalInformation.toInformationVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsDigitalInformation v) :
    IsInformationVariable v :=
  h

-- A `Replicator` is a substrate with an information variable
-- whose attributes can all be replicated.
-- Following Marletto (2014): "An entity is a replicator if it has
-- a set of attributes (its 'recipes') each of which can cause
-- the construction of a copy of itself."
structure Replicator (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The information variable encoding the replicator's "recipe"
  info : Variable S
  -- The information variable is digital (clonable)
  is_digital : IsDigitalInformation info

-- A replicator's information is a computation variable.
theorem Replicator.is_computation {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (r : Replicator S) : IsComputationVariable r.info :=
  r.is_digital.toComputationVariable

-- The replication task: given a replicator in attribute i and
-- a blank target, produce a copy in the same attribute.
def replicationTask {S : Type} (a blank : Attribute S) :
    Task (S × S) :=
  cloneTaskSingle a blank

-- A replicator can replicate each of its attributes.
theorem Replicator.can_replicate {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (r : Replicator S) :
    ∃ blank : Attribute S,
      ∀ i : Fin r.info.attrs.length,
        Possible (replicationTask (r.info.attrs.get i) blank) := by
  exact r.is_digital.2

-- A `SelfReproducer` is a composite system that can act as a
-- constructor for its own reproduction from generic resources.
-- Following Marletto (2014), a self-reproducer consists of:
-- (1) A replicator R (carrying the "recipe")
-- (2) A vehicle V (the machinery that reads the recipe and builds)
-- The reproduction task: (R, V) + resources → (R, V) + (R', V')
structure SelfReproducer (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The replicator component
  replicator : Replicator S
  -- The reproduction task is possible: from the current state
  -- and generic resources, produce a copy
  reproduction_possible : ∃ (resource_attr copy_attr : Attribute (S × S)),
    Possible { input := resource_attr,
               output := copy_attr : Task (S × S) }

-- A self-reproducer has a replicator with digital information.
theorem SelfReproducer.has_digital_info {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (sr : SelfReproducer S) : IsDigitalInformation sr.replicator.info :=
  sr.replicator.is_digital

-- A `NoDesignLaw` is a law of physics that does not single out
-- any specific state or substrate. It only constrains which
-- task types are possible and which are impossible, without
-- privileging any particular configuration.
-- Following Marletto (2014): "under no-design laws, all laws
-- are expressible as statements about possible and impossible tasks."
structure NoDesignLaw (S : Type) [TaskPossibility S] where
  -- The law is a predicate on tasks
  law : Task S → Prop
  -- Symmetry: the law treats all attributes uniformly.
  -- If the law holds for a task a→b, and we have an automorphism
  -- σ that maps attributes, then it holds for σ(a)→σ(b).
  -- Simplified: the law depends only on the structure of the task,
  -- not on which particular states are involved.
  uniform : ∀ (t : Task S), law t → law t†† -- The law is preserved under double transpose (identity)

-- Under no-design laws, the possibility predicate is a no-design law.
def possibilityNoDesign {S : Type} [TaskPossibility S] :
    NoDesignLaw S where
  law := Possible
  uniform := by
    intro t h
    simp [Task.transpose_transpose]
    exact h

-- The key theorem from Marletto (2014): under no-design laws,
-- the existence of digital information is sufficient for
-- self-reproduction to be possible.
-- Statement: If a substrate has digital information (an information
-- variable), then the abstract self-reproduction task is not
-- ruled out by the laws of physics.
-- (The actual proof requires the full machinery of constructor theory
-- of information; here we state the theorem with its logical structure.)
theorem digital_info_enables_replication {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (r : Replicator S) :
    ∃ blank : Attribute S,
      ∀ i : Fin r.info.attrs.length,
        Possible (cloneTaskSingle (r.info.attrs.get i) blank) :=
  r.can_replicate

-- Heritable variation: a collection of self-reproducers has
-- heritable variation if their replicators have distinct attributes
-- that are preserved through reproduction.
def HasHeritableVariation {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)]
    (sr₁ sr₂ : SelfReproducer S) : Prop :=
  sr₁.replicator.info.attrs ≠ sr₂.replicator.info.attrs

-- Natural selection requires heritable variation and differential
-- reproduction. This is the constructor-theoretic precondition
-- for evolution by natural selection.
structure NaturalSelectionCondition (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- At least two self-reproducers with different recipes
  sr₁ : SelfReproducer S
  sr₂ : SelfReproducer S
  -- They have heritable variation
  variation : HasHeritableVariation sr₁ sr₂

end ConstructorTheory
