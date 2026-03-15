/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Information.Basic
import ConstructorTheory.Information.InformationMedium
import ConstructorTheory.Principles.Basic

/-!
# Observables and Measurement

Formalizes the constructor-theoretic notions of distinguishability,
measurement, and observables, following Deutsch & Marletto (2014).

In constructor theory, measurement is not a primitive concept but
is derived from the possibility of certain tasks. An observable is
a variable whose attributes can be reliably distinguished by a
physical process (constructor).

## Main definitions

* `IsDistinguishable` - Two attributes that can be reliably told apart
* `IsMeasurableVariable` - A variable whose attributes can be measured
* `IsObservable` - A measurable variable producing sharp outcomes
* `IsInformationObservable` - An observable that is also an information variable

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- Two attributes are `Distinguishable` if there exists a task
-- that maps them to distinct outcomes on an information medium.
-- Formally: there exist two disjoint output attributes o₁, o₂
-- such that the tasks a₁→o₁ and a₂→o₂ are both possible.
def IsDistinguishable {S : Type} [TaskPossibility S]
    (a₁ a₂ : Attribute S) : Prop :=
  ∃ (o₁ o₂ : Attribute S),
    Attribute.Disjoint o₁ o₂ ∧
    Possible { input := a₁, output := o₁ : Task S } ∧
    Possible { input := a₂, output := o₂ : Task S }

-- Distinguishability is symmetric.
theorem IsDistinguishable.symm {S : Type} [TaskPossibility S]
    {a₁ a₂ : Attribute S} (h : IsDistinguishable a₁ a₂) :
    IsDistinguishable a₂ a₁ := by
  obtain ⟨o₁, o₂, hdisj, h₁, h₂⟩ := h
  exact ⟨o₂, o₁, hdisj.symm, h₂, h₁⟩

-- Disjoint attributes in a computation variable are distinguishable
-- (in a ConstructorUniverse), since the identity task on each is possible.
theorem computation_variable_attrs_distinguishable {S : Type}
    [ConstructorUniverse S] {v : Variable S}
    (_hv : IsComputationVariable v) (i j : Fin v.attrs.length) (hij : i ≠ j) :
    IsDistinguishable (v.attrs.get i) (v.attrs.get j) := by
  refine ⟨v.attrs.get i, v.attrs.get j, v.pairwise_disjoint i j hij, ?_, ?_⟩
  · exact identity_task_possible (v.attrs.get i)
  · exact identity_task_possible (v.attrs.get j)

-- A variable is `Measurable` if each of its attributes can be
-- mapped to a corresponding attribute of an output variable
-- (an information medium) without disturbing the input.
-- The measurement task preserves the input and writes the result.
def IsMeasurableVariable {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  ∃ (out : Variable S) (blank : Attribute S),
    out.attrs.length = v.attrs.length ∧
    ∀ (i : Fin v.attrs.length) (hi : i.val < out.attrs.length),
      Possible { input := Attribute.prod (v.attrs.get i) blank,
                 output := Attribute.prod (v.attrs.get i)
                   (out.attrs.get ⟨i.val, hi⟩) : Task (S × S) }

-- An `Observable` is a variable where measurement produces
-- sharp outcomes: each input attribute maps to exactly one
-- output attribute, and different inputs produce distinguishable outputs.
-- This is the constructor-theoretic formalization of quantum observables.
def IsObservable {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  IsMeasurableVariable v ∧
  -- Sharp outcomes: all pairs of attributes are distinguishable
  ∀ i j : Fin v.attrs.length, i ≠ j →
    IsDistinguishable (v.attrs.get i) (v.attrs.get j)

-- An observable is measurable.
theorem IsObservable.toMeasurable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsObservable v) :
    IsMeasurableVariable v :=
  h.1

-- An observable has distinguishable attributes.
theorem IsObservable.attrs_distinguishable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsObservable v)
    (i j : Fin v.attrs.length) (hij : i ≠ j) :
    IsDistinguishable (v.attrs.get i) (v.attrs.get j) :=
  h.2 i j hij

-- An `InformationObservable` is both an observable and an
-- information variable. This is the strongest notion: the
-- variable can be measured, its attributes are distinguishable,
-- and it can be cloned.
def IsInformationObservable {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  IsObservable v ∧ IsInformationVariable v

-- An information observable is an observable.
theorem IsInformationObservable.toObservable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsInformationObservable v) :
    IsObservable v :=
  h.1

-- An information observable is an information variable.
theorem IsInformationObservable.toInformationVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsInformationObservable v) :
    IsInformationVariable v :=
  h.2

-- An information observable is a computation variable.
theorem IsInformationObservable.toComputationVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsInformationObservable v) :
    IsComputationVariable v :=
  h.2.toComputationVariable

-- A superinformation medium has two information observables whose
-- union is not an information observable.
-- This strengthens the existing `IsSuperinformationMedium` by
-- requiring the incompatible variables to be observables.
def HasIncompatibleObservables (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] : Prop :=
  ∃ (v₁ v₂ : Variable S),
    IsInformationObservable v₁ ∧
    IsInformationObservable v₂ ∧
    ∀ (v_union : Variable S),
      (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
      (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
      ¬ IsInformationObservable v_union

-- Incompatible observables imply superinformation: if two
-- information observables have an incompatible union (as observables),
-- then their underlying information variables also have an incompatible
-- union (as information variables), since IsInformationObservable
-- is strictly stronger than IsInformationVariable.
theorem HasIncompatibleObservables.toSuperinformation {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : HasIncompatibleObservables S) : IsSuperinformationMedium S := by
  obtain ⟨v₁, v₂, ho₁, ho₂, hincompat⟩ := h
  refine ⟨⟨v₁, ho₁.toInformationVariable⟩, v₁, v₂,
    ho₁.toInformationVariable, ho₂.toInformationVariable, ?_⟩
  intro v_union h₁ h₂ hinfo
  -- If v_union were an information variable, it would also be an
  -- information observable (since it's measurable via its clone task
  -- and has distinguishable attributes from its computation variable property).
  -- But hincompat says no such information observable exists.
  -- We use a weaker sufficient condition: show the incompatibility
  -- directly by constructing the observability.
  apply hincompat v_union h₁ h₂
  constructor
  · constructor
    · -- Measurability: use the clone task as measurement
      obtain ⟨_, blank, hclone⟩ := hinfo
      exact ⟨v_union, blank, rfl, fun i hi => hclone i⟩
    · -- Distinguishability: use computation variable properties
      intro i j hij
      exact ⟨v_union.attrs.get i, v_union.attrs.get j,
        v_union.pairwise_disjoint i j hij,
        hinfo.toComputationVariable i i,
        hinfo.toComputationVariable j j⟩
  · exact hinfo

-- A `BooleanVariable` is a two-element variable: {x, x̄} where
-- x̄ is the complement of x.
def IsBooleanVariable {S : Type} (v : Variable S) : Prop :=
  v.attrs.length = 2

-- A boolean variable has exactly two attributes.
theorem IsBooleanVariable.two_attrs {S : Type}
    {v : Variable S} (h : IsBooleanVariable v) :
    v.attrs.length = 2 :=
  h

end ConstructorTheory
