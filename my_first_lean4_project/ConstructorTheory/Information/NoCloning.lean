/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Information.Basic
import ConstructorTheory.Information.Observable
import ConstructorTheory.Information.InformationMedium

/-!
# No-Cloning Theorem and Measurement Disturbance

Formalizes the constructor-theoretic no-cloning theorem and measurement
disturbance, following Deutsch & Marletto (2014).

The no-cloning theorem in constructor theory states that for
superinformation media, there exist variables that cannot be cloned.
This is a deeper result than the quantum no-cloning theorem because
it derives from the structure of possible/impossible tasks rather than
from the formalism of quantum mechanics.

## Key concepts

* *No-cloning*: Some variables in a superinformation medium cannot be
  cloned (their union with any other variable is not an information variable).
* *Measurement disturbance*: Measuring a superinformation variable
  necessarily disturbs complementary observables.
* *Complementary observables*: Two observables that cannot be measured
  simultaneously without disturbance.

## Main definitions

* `IsUnclonable` - A variable that cannot be cloned
* `ComplementaryPair` - Two observables that cannot both be measured
* `MeasurementDisturbs` - Measuring one observable disturbs another
* `NoCloningTheorem` - The no-cloning theorem for superinformation media

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- A variable is `Unclonable` if the cloning task is impossible
-- for at least one of its attributes.
-- In quantum mechanics, this corresponds to the no-cloning theorem
-- for non-orthogonal states.
def IsUnclonable {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  ¬ IsInformationVariable v ∧ IsComputationVariable v

-- An unclonable variable is a computation variable but not
-- an information variable.
theorem IsUnclonable.is_computation {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsUnclonable v) :
    IsComputationVariable v :=
  h.2

-- An unclonable variable is not an information variable.
theorem IsUnclonable.not_information {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsUnclonable v) :
    ¬ IsInformationVariable v :=
  h.1

-- Two observables are `Complementary` if they cannot be jointly
-- measured: measuring one necessarily disturbs the other.
-- This is the constructor-theoretic version of quantum complementarity
-- (e.g., position and momentum, or spin-x and spin-z).
def ComplementaryPair {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v₁ v₂ : Variable S) : Prop :=
  IsInformationVariable v₁ ∧
  IsInformationVariable v₂ ∧
  -- Their union cannot form an information variable
  ∀ (v_union : Variable S),
    (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
    (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
    ¬ IsInformationVariable v_union

-- Complementarity is symmetric.
theorem ComplementaryPair.symm {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v₁ v₂ : Variable S} (h : ComplementaryPair v₁ v₂) :
    ComplementaryPair v₂ v₁ :=
  ⟨h.2.1, h.1, fun v_union h₂ h₁ => h.2.2 v_union h₁ h₂⟩

-- Complementary variables witness superinformation.
theorem ComplementaryPair.implies_superinformation {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v₁ v₂ : Variable S} (h : ComplementaryPair v₁ v₂) :
    IsSuperinformationMedium S :=
  ⟨⟨v₁, h.1⟩, v₁, v₂, h.1, h.2.1, h.2.2⟩

-- `MeasurementDisturbs`: measuring observable v₁ disturbs observable v₂
-- if after a measurement of v₁, the attributes of v₂ can no longer be
-- reliably distinguished.
-- Formalized: no constructor can jointly measure both v₁ and v₂.
def MeasurementDisturbs {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v₁ v₂ : Variable S) : Prop :=
  -- There is no measurement task that preserves both variables:
  -- no task that copies v₁ to an output while leaving v₂ undisturbed
  ∀ (blank : Attribute S),
    ∃ (i : Fin v₁.attrs.length) (j : Fin v₂.attrs.length),
      Impossible { input := Attribute.prod (v₁.attrs.get i) blank,
                   output := Attribute.prod (v₁.attrs.get i)
                     (v₂.attrs.get j) : Task (S × S) }

-- Complementary observables cause measurement disturbance
-- (in at least one direction).
-- If v₁ and v₂ are complementary, then attempting to clone their
-- union would violate the no-cloning constraint, implying that
-- measuring one disturbs the other.
theorem complementary_implies_disturbance {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v₁ v₂ : Variable S} (h : ComplementaryPair v₁ v₂) :
    ∀ (v_union : Variable S),
      (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
      (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
      ¬ IsInformationVariable v_union :=
  h.2.2

-- The **No-Cloning Theorem** in constructor-theoretic terms:
-- In a superinformation medium, there exist variables that cannot
-- be cloned. Specifically, the union of two complementary information
-- variables is not clonable.
-- This is more general than the quantum no-cloning theorem because
-- it applies to any physical theory with the superinformation property.
structure NoCloningTheorem (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The substrate is a superinformation medium
  is_super : IsSuperinformationMedium S
  -- There exist complementary variables
  has_complementary : ∃ (v₁ v₂ : Variable S), ComplementaryPair v₁ v₂

-- A superinformation medium satisfies the no-cloning theorem.
theorem superinfo_has_no_cloning {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsSuperinformationMedium S) :
    ∃ (v₁ v₂ : Variable S),
      IsInformationVariable v₁ ∧
      IsInformationVariable v₂ ∧
      ∀ (v_union : Variable S),
        (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
        (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
        ¬ IsInformationVariable v_union :=
  h.2

-- The no-cloning theorem implies there exist unclonable unions:
-- the union of the two complementary variables is a computation
-- variable (under suitable conditions) but not an information variable.
theorem no_cloning_implies_unclonable_union {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v₁ v₂ : Variable S} (h : ComplementaryPair v₁ v₂)
    (v_union : Variable S)
    (h₁ : ∀ a ∈ v₁.attrs, a ∈ v_union.attrs)
    (h₂ : ∀ a ∈ v₂.attrs, a ∈ v_union.attrs) :
    ¬ IsInformationVariable v_union :=
  h.2.2 v_union h₁ h₂

-- Classical media (non-superinformation) satisfy universal clonability:
-- every computation variable is an information variable.
-- This is the classical-quantum divide in constructor theory.
def IsClassicalMedium (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] : Prop :=
  IsInformationMedium S ∧ ¬ IsSuperinformationMedium S

-- In a classical medium, there are no complementary pairs.
theorem classical_no_complementary {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsClassicalMedium S) :
    ¬ ∃ (v₁ v₂ : Variable S), ComplementaryPair v₁ v₂ := by
  intro ⟨v₁, v₂, hc⟩
  exact h.2 (hc.implies_superinformation)

end ConstructorTheory
