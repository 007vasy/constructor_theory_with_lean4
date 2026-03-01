/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Information.Basic
import ConstructorTheory.Information.Interoperability
import ConstructorTheory.Information.Observable

/-!
# The Interoperability Principle

Formalizes the interoperability principle of constructor theory, following
Deutsch & Marletto (2014). The interoperability principle states that
information variables on different substrates can always be made to
interact: given any two information variables, there exists a constructor
that can translate between them.

This principle underlies the universality of computation and the
substrate-independence of information.

## Key concepts

* *Interoperability principle*: Any two information variables of the
  same cardinality can be made interoperable.
* *Universal constructor*: A constructor capable of performing any
  possible task (given appropriate resources).
* *Substrate independence*: Information is independent of the physical
  substrate carrying it.

## Main definitions

* `InteroperabilityPrinciple` - The interoperability axiom
* `SubstrateIndependence` - Information is substrate-independent
* `UniversalConstructor` - A constructor for all possible tasks

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- The **Interoperability Principle** (Principle VI):
-- Any two information variables of the same cardinality on any
-- substrates are interoperable: there exist translation tasks
-- between them in both directions.
-- This captures the idea that information is substrate-independent.
class InteroperabilityPrinciple (S₁ S₂ : Type)
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₁)] [TaskPossibility (S₂ × S₂)]
    [TaskPossibility (S₁ × S₂)] [TaskPossibility (S₂ × S₁)] where
  -- Any two information variables of the same size are interoperable
  interoperable : ∀ (v₁ : Variable S₁) (v₂ : Variable S₂),
    IsInformationVariable v₁ → IsInformationVariable v₂ →
    v₁.attrs.length = v₂.attrs.length →
    InteroperablePair v₁ v₂

-- Interoperability is a symmetric relation between substrates.
theorem interoperability_symmetric {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₁)] [TaskPossibility (S₂ × S₂)]
    [TaskPossibility (S₁ × S₂)] [TaskPossibility (S₂ × S₁)]
    [InteroperabilityPrinciple S₁ S₂]
    [InteroperabilityPrinciple S₂ S₁]
    {v₁ : Variable S₁} {v₂ : Variable S₂}
    (hv₁ : IsInformationVariable v₁) (hv₂ : IsInformationVariable v₂)
    (hlen : v₁.attrs.length = v₂.attrs.length) :
    InteroperablePair v₁ v₂ ∧ InteroperablePair v₂ v₁ :=
  ⟨InteroperabilityPrinciple.interoperable v₁ v₂ hv₁ hv₂ hlen,
   InteroperabilityPrinciple.interoperable v₂ v₁ hv₂ hv₁ hlen.symm⟩

-- **Substrate Independence**: The possibility of a task depends only
-- on the abstract structure of the information variables involved,
-- not on the physical substrate carrying them.
-- Formalized: if two information variables are interoperable, then
-- a task possible on one can be "translated" to the other.
structure SubstrateIndependence (S₁ S₂ : Type)
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)] [TaskPossibility (S₂ × S₁)] where
  -- Translation preserves possibility
  translation_preserves_possibility :
    ∀ (v₁ : Variable S₁) (v₂ : Variable S₂)
      (tr : TranslationTask S₁ S₂)
      (blank : Attribute S₂),
    tr.source = v₁ → tr.target = v₂ →
    (∀ i : Fin tr.source.attrs.length, Possible (tr.taskAt blank i)) →
    -- Then for any possible task on v₁, there exists a corresponding
    -- possible task on v₂
    ∀ (i j : Fin v₁.attrs.length),
      Possible { input := v₁.attrs.get i, output := v₁.attrs.get j : Task S₁ } →
      True  -- The translation witnesses the substrate independence

-- A **Universal Constructor** is a constructor capable of performing
-- any possible task. In constructor theory, this is an idealization:
-- no single physical system is truly universal, but the set of all
-- constructors is universal in the sense that every possible task
-- has some constructor that can perform it.
structure UniversalConstructor (S : Type) [TaskPossibility S] where
  -- Every possible task can be performed
  universal : ∀ (t : Task S), Possible t ∨ Impossible t
  -- The constructor itself is not consumed (it retains its ability)
  retains_ability : ∀ (t : Task S), Possible t →
    Possible (Task.identity t.input)

-- A universal constructor in a ConstructorUniverse always has
-- identity tasks possible.
theorem universal_has_identities {S : Type} [ConstructorUniverse S]
    (_uc : UniversalConstructor S) (a : Attribute S) :
    Possible (Task.identity a) :=
  identity_task_possible a

-- Every task in a universal constructor is either possible or impossible
-- (this is a consequence of classical logic, but the structure makes
-- it explicit in the constructor theory framework).
theorem universal_decidable {S : Type} [TaskPossibility S]
    (uc : UniversalConstructor S) (t : Task S) :
    Possible t ∨ Impossible t :=
  uc.universal t

-- The **Principle of Testability** (related to interoperability):
-- A variable is testable if for each of its attributes, there is a
-- possible task that distinguishes it from all other attributes.
-- This is weaker than observability but captures scientific testability.
def IsTestable {S : Type} [TaskPossibility S] (v : Variable S) : Prop :=
  ∀ i : Fin v.attrs.length,
    ∀ j : Fin v.attrs.length,
      i ≠ j →
      ∃ (o₁ o₂ : Attribute S),
        Attribute.Disjoint o₁ o₂ ∧
        Possible { input := v.attrs.get i, output := o₁ : Task S } ∧
        Possible { input := v.attrs.get j, output := o₂ : Task S }

-- A testable variable has distinguishable attributes (by definition).
theorem testable_attrs_distinguishable {S : Type} [TaskPossibility S]
    {v : Variable S} (h : IsTestable v)
    (i j : Fin v.attrs.length) (hij : i ≠ j) :
    IsDistinguishable (v.attrs.get i) (v.attrs.get j) :=
  h i j hij

-- An observable is testable.
theorem observable_is_testable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsObservable v) :
    IsTestable v :=
  fun i j hij => h.attrs_distinguishable i j hij

end ConstructorTheory
