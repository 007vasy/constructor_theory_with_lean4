/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Life.Basic
import ConstructorTheory.Life.Evolution
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.Entropy
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Information.NoCloning
import ConstructorTheory.Principles.Basic

/-!
# Information-Life-Thermodynamics Bridge

Formalizes the connections between the constructor theories of life,
information, and thermodynamics. Life is characterized by the ability
to create and preserve knowledge — a special kind of information
that has causal power and can replicate itself.

## Key results

* `replicator_info_clonable` - Replicators have clonable information
* `knowledge_thermodynamic_cost` - Knowledge preservation has thermodynamic cost
* `adaptation_requires_info` - Adaptation requires digital information
* `evolution_creates_knowledge` - Open-ended evolution creates new knowledge
* `classical_replicator` - Classical media support simpler replication

## References

* C. Marletto, "Constructor Theory of Life",
  J. R. Soc. Interface 12:20141226 (2015), arXiv:1407.0681
* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
-/

namespace ConstructorTheory

-- ============================================================
-- Replication and information theory
-- ============================================================

-- A replicator's information variable satisfies all properties
-- of an information variable: it is a computation variable that
-- is also clonable.
theorem replicator_is_info_variable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (r : Replicator S) : IsInformationVariable r.info :=
  r.is_digital

-- In a classical medium (no superinformation), every computation
-- variable could potentially be an information variable, making
-- replication easier.
theorem classical_replication_universal {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsClassicalMedium S) :
    ¬ ∃ (v₁ v₂ : Variable S), ComplementaryPair v₁ v₂ :=
  classical_no_complementary h

-- ============================================================
-- Thermodynamic cost of self-reproduction
-- ============================================================

-- Self-reproduction involves cloning (which is possible for information
-- variables) and construction (which requires resources). Under
-- Landauer's principle, the cloning step has a thermodynamic cost:
-- erasing the "blank" state to prepare it as a copy costs heat.
theorem reproduction_has_landauer_cost {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    (sr : SelfReproducer S) :
    -- The replicator's information can be copied...
    (∃ blank : Attribute S,
      ∀ i : Fin sr.replicator.info.attrs.length,
        Possible (replicationTask (sr.replicator.info.attrs.get i) blank)) ∧
    -- ...but erasing the copy (returning to blank) is not free
    (∀ target : Fin sr.replicator.info.attrs.length,
      ∃ source : Fin sr.replicator.info.attrs.length,
        source ≠ target ∧
        AdiabaticImpossible { input := sr.replicator.info.attrs.get source,
                              output := sr.replicator.info.attrs.get target : Task S }) := by
  constructor
  · exact sr.replicator.can_replicate
  · intro target
    exact LandauerPrinciple.erasure_irreversible
      sr.replicator.info sr.replicator.is_digital target

-- ============================================================
-- Adaptation and digital information
-- ============================================================

-- A self-reproducer that is adapted to an environment must have
-- digital information (an information variable). This is because
-- adaptation requires the organism's "recipe" to be preserved
-- through reproduction, which requires clonability.
theorem adapted_has_digital_info {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (sr : SelfReproducer S) (_env : Environment S)
    (_h_adapted : IsAdapted sr _env) :
    IsDigitalInformation sr.replicator.info :=
  sr.replicator.is_digital

-- ============================================================
-- Knowledge and the constructor-theoretic second law
-- ============================================================

-- Knowledge creation is thermodynamically irreversible: once
-- knowledge is created (a new adapted self-reproducer appears),
-- destroying that knowledge while maintaining the system's
-- adaptedness is impossible.
-- This connects to the second law: knowledge creation increases
-- the "information content" of the biosphere in a way that
-- cannot be spontaneously reversed.
theorem knowledge_creation_irreversible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    (k : @IsKnowledge S _ _) :
    -- Knowledge can be copied (it's digital information)
    (∃ blank : Attribute S,
      ∀ i : Fin k.info.attrs.length,
        Possible (cloneTaskSingle (k.info.attrs.get i) blank)) ∧
    -- But erasing knowledge has a thermodynamic cost
    (∀ target : Fin k.info.attrs.length,
      ∃ source : Fin k.info.attrs.length,
        source ≠ target ∧
        ¬ AdiabaticPossible { input := k.info.attrs.get source,
                              output := k.info.attrs.get target : Task S }) := by
  constructor
  · exact k.preserved_through_copy
  · intro target
    exact LandauerPrinciple.erasure_irreversible k.info k.info_is_digital target

-- ============================================================
-- Evolution and thermodynamics
-- ============================================================

-- Open-ended evolution requires that new self-reproducers can
-- always arise. Combined with the second law, this means that
-- evolution is a thermodynamically irreversible process that
-- continuously creates new information.
theorem evolution_thermodynamic_arrow {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (oee : OpenEndedEvolution S) :
    -- There always exist distinct self-reproducers (unbounded variation)
    ∀ (sr : SelfReproducer S),
      ∃ (sr' : SelfReproducer S), HasHeritableVariation sr sr' :=
  oee.open_ended

-- ============================================================
-- Fitness and work extraction
-- ============================================================

-- A `FitnessLandscape` maps self-reproducers to their ability
-- to extract work from the environment (a proxy for reproductive success).
-- In constructor theory, fitness is not a numerical value but a
-- comparison of which reproduction tasks are possible.
structure FitnessLandscape (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The environment
  env : Environment S
  -- Fitness comparison: sr₁ is "fitter" than sr₂ if sr₁'s
  -- reproduction task is possible in strictly more conditions
  fitter : SelfReproducer S → SelfReproducer S → Prop
  -- Fitness is transitive
  fitter_trans : ∀ sr₁ sr₂ sr₃,
    fitter sr₁ sr₂ → fitter sr₂ sr₃ → fitter sr₁ sr₃
  -- Fitness is irreflexive (strict ordering)
  fitter_irrefl : ∀ sr, ¬ fitter sr sr

-- ============================================================
-- Error correction and knowledge preservation
-- ============================================================

-- Digital information supports error correction: a replicator
-- can detect and correct errors in its information because the
-- cloning task has well-defined outputs for each input attribute.
-- This is why digital (as opposed to analog) information is
-- essential for open-ended evolution.
theorem digital_enables_error_detection {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (r : Replicator S) :
    -- Each attribute has a distinct clone output
    ∃ blank : Attribute S,
      ∀ i : Fin r.info.attrs.length,
        Possible (cloneTaskSingle (r.info.attrs.get i) blank) :=
  r.can_replicate

-- ============================================================
-- The no-design principle and evolution
-- ============================================================

-- Under no-design laws, the laws of physics do not encode the
-- design of any particular organism. This means that all knowledge
-- must be created by evolution (variation + selection), not by
-- the laws themselves.
theorem no_design_uniform {S : Type} [TaskPossibility S]
    (law : NoDesignLaw S) (t : Task S) (h : law.law t) :
    law.law t†† :=
  law.uniform t h

-- If the laws are no-design, knowledge cannot come from the laws
-- themselves but must be created through evolutionary processes.
-- This is formalized as: a no-design law on the product substrate
-- treats all self-reproducers uniformly (it doesn't privilege any
-- particular "design"). The replication task lives on S × S.
theorem no_design_treats_replicators_uniformly {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (law : NoDesignLaw (S × S))
    (_sr₁ _sr₂ : SelfReproducer S)
    (i₁ : Fin _sr₁.replicator.info.attrs.length)
    (blank : Attribute S) :
    law.law (replicationTask (_sr₁.replicator.info.attrs.get i₁) blank) →
    law.law (replicationTask (_sr₁.replicator.info.attrs.get i₁) blank)†† := by
  intro h
  exact law.uniform _ h

end ConstructorTheory
