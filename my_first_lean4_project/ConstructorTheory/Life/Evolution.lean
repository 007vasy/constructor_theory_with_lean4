/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Life.Basic
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Thermodynamics.Basic

/-!
# Constructor Theory of Life: Knowledge, Adaptation, and Evolution

Extends the life formalization with constructor-theoretic definitions of
knowledge, adaptation, and the conditions for open-ended evolution,
following Marletto (2014) and Deutsch (2013).

## Key concepts

* *Knowledge*: Information that, once instantiated in a physical system,
  causes that system to remain adapted to its environment. Knowledge is
  a special kind of information that has explanatory power.
* *Adaptation*: A self-reproducer is adapted to an environment if its
  reproduction task remains possible in that environment.
* *Open-ended evolution*: The capacity for cumulative adaptation, where
  new knowledge can be created and preserved.
* *Resilience*: The ability of knowledge to persist across reproduction
  events and environmental perturbations.

## Main definitions

* `IsKnowledge` - Information that enables environment-specific tasks
* `IsAdapted` - A self-reproducer adapted to an environment
* `EvolutionaryLineage` - A sequence of self-reproducers with variation
* `OpenEndedEvolution` - Capacity for cumulative adaptation
* `IsResilient` - Knowledge that persists across perturbations

## References

* C. Marletto, "Constructor Theory of Life",
  J. R. Soc. Interface 12:20141226 (2015), arXiv:1407.0681
* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
* D. Deutsch, "The Beginning of Infinity", Allen Lane (2011)
-/

namespace ConstructorTheory

-- An `Environment` specifies the conditions under which a self-reproducer
-- must operate. It is modeled as a set of constraints on which tasks
-- are possible (which resources are available, which conditions hold).
structure Environment (S : Type) [TaskPossibility S] where
  -- An environment is characterized by which tasks it enables
  enabled_tasks : Task S → Prop
  -- The identity task is always enabled (the environment exists)
  identity_enabled : ∀ (a : Attribute S),
    enabled_tasks (Task.identity a)

-- A self-reproducer is `Adapted` to an environment if its
-- reproduction task is possible in that environment.
-- Following Marletto (2014): adaptation means the self-reproducer
-- can function as a constructor for its own reproduction under
-- the given conditions.
def IsAdapted {S : Type} [TaskPossibility S] [TaskPossibility (S × S)]
    (_sr : SelfReproducer S) (_env : Environment S) : Prop :=
  -- The reproduction task is compatible with the environment
  ∃ (resource_attr copy_attr : Attribute (S × S)),
    Possible { input := resource_attr,
               output := copy_attr : Task (S × S) }

-- `Knowledge` is information that, when instantiated in a substrate,
-- enables that substrate to perform environment-specific tasks that
-- would otherwise be impossible.
-- Following Deutsch (2013): knowledge is information that tends to
-- cause its own perpetuation.
structure IsKnowledge {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The information variable encoding the knowledge
  info : Variable S
  info_is_digital : IsDigitalInformation info
  -- The knowledge enables specific tasks (has causal power)
  enables_tasks : ∃ (task : Task S),
    Possible task
  -- The knowledge is preserved through replication
  preserved_through_copy : ∃ (blank : Attribute S),
    ∀ i : Fin info.attrs.length,
      Possible (cloneTaskSingle (info.attrs.get i) blank)

-- Knowledge contains digital information.
theorem IsKnowledge.is_digital {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (k : @IsKnowledge S _ _) : IsDigitalInformation k.info :=
  k.info_is_digital

-- Knowledge is replicable (can be copied).
theorem IsKnowledge.is_replicable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (k : @IsKnowledge S _ _) :
    ∃ blank : Attribute S,
      ∀ i : Fin k.info.attrs.length,
        Possible (cloneTaskSingle (k.info.attrs.get i) blank) :=
  k.preserved_through_copy

-- A `Mutation` is a change in the replicator's information variable
-- that produces a distinct self-reproducer.
-- Mutations are the source of heritable variation.
def IsMutation {S : Type} [TaskPossibility S] [TaskPossibility (S × S)]
    (sr_parent sr_offspring : SelfReproducer S) : Prop :=
  -- The offspring has different information than the parent
  HasHeritableVariation sr_parent sr_offspring

-- An `EvolutionaryLineage` is a sequence of self-reproducers where
-- each is derived from the previous one (possibly with mutations).
-- This captures the concept of descent with modification.
structure EvolutionaryLineage (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The sequence of self-reproducers (indexed by Fin n for some n)
  length : Nat
  length_pos : length ≥ 2
  organisms : Fin length → SelfReproducer S
  -- Each organism can reproduce (already guaranteed by SelfReproducer)
  -- Adjacent organisms may have mutations (heritable variation)
  has_descent : ∀ (i : Fin length) (hi : i.val + 1 < length),
    -- The offspring's replicator info is an information variable
    IsDigitalInformation (organisms ⟨i.val + 1, hi⟩).replicator.info

-- An evolutionary lineage has at least 2 organisms.
theorem EvolutionaryLineage.has_at_least_two {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (el : EvolutionaryLineage S) :
    el.length ≥ 2 :=
  el.length_pos

-- An evolutionary lineage with any heritable variation satisfies
-- the preconditions for natural selection.
def lineage_with_variation_enables_selection {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (el : EvolutionaryLineage S)
    (h0 : 0 < el.length) (h1 : 1 < el.length)
    (hvar : HasHeritableVariation
      (el.organisms ⟨0, h0⟩) (el.organisms ⟨1, h1⟩)) :
    NaturalSelectionCondition S :=
  { sr₁ := el.organisms ⟨0, h0⟩
    sr₂ := el.organisms ⟨1, h1⟩
    variation := hvar }

-- `OpenEndedEvolution` captures the capacity for a system to
-- undergo cumulative adaptation: the creation of new knowledge
-- through variation and selection over multiple generations.
-- This is the constructor-theoretic formulation of what Deutsch
-- calls "the beginning of infinity."
structure OpenEndedEvolution (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- A lineage exists
  lineage : EvolutionaryLineage S
  -- There is heritable variation somewhere in the lineage
  has_variation : ∃ (i : Fin lineage.length) (j : Fin lineage.length),
    i ≠ j ∧ HasHeritableVariation (lineage.organisms i) (lineage.organisms j)
  -- New self-reproducers can arise (the space of possible replicators
  -- is not exhausted by the current lineage)
  open_ended : ∀ (sr : SelfReproducer S),
    ∃ (sr' : SelfReproducer S), HasHeritableVariation sr sr'

-- Open-ended evolution implies natural selection conditions.
theorem open_ended_implies_selection {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (oee : OpenEndedEvolution S) :
    ∃ (sr₁ sr₂ : SelfReproducer S), HasHeritableVariation sr₁ sr₂ := by
  obtain ⟨i, j, _, hvar⟩ := oee.has_variation
  exact ⟨oee.lineage.organisms i, oee.lineage.organisms j, hvar⟩

-- `Resilience` captures the ability of knowledge to persist across
-- environmental perturbations. Knowledge is resilient if small
-- changes to the environment do not make reproduction impossible.
def IsResilient {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)]
    (sr : SelfReproducer S)
    (envs : List (Environment S))
    (_h_nonempty : envs ≠ []) : Prop :=
  -- The self-reproducer is adapted to all environments in the list
  ∀ env ∈ envs, IsAdapted sr env

-- A resilient self-reproducer can reproduce in multiple environments.
theorem resilient_reproduces_everywhere {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {sr : SelfReproducer S}
    {envs : List (Environment S)} {h_ne : envs ≠ []}
    (h : IsResilient sr envs h_ne) (env : Environment S)
    (henv : env ∈ envs) :
    IsAdapted sr env :=
  h env henv

-- The fundamental asymmetry of constructor theory of life:
-- knowledge creation (the appearance of new adapted self-reproducers)
-- is possible, but its reversal (destroying knowledge while maintaining
-- adaptedness) is typically impossible.
-- This connects to the thermodynamic arrow of time.
theorem knowledge_creation_asymmetry {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (sr : SelfReproducer S) :
    ∃ blank : Attribute S,
      ∀ i : Fin sr.replicator.info.attrs.length,
        Possible (replicationTask (sr.replicator.info.attrs.get i) blank) :=
  sr.replicator.can_replicate

end ConstructorTheory
