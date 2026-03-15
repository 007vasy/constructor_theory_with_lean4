/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Information.Basic
import ConstructorTheory.Composition

/-!
# Interoperability of Information Variables

Two information variables on different substrates are *interoperable* if
there exists a constructor that can copy the state of one variable to the other,
using a "translation" task.

Interoperability is a key concept in the constructor theory of information:
it captures when two physical systems can be used to represent the same
abstract information.

## Main definitions

* `TranslationTask` - A task that maps attribute i of one variable to
  attribute i of another
* `InteroperablePair` - Two variables on different substrates that are
  mutually translatable
* `SelfInteroperable` - A variable that is interoperable with itself
  (equivalent to being a computation variable)

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015), Section 5
-/

namespace ConstructorTheory

-- A translation task from variable v₁ on S₁ to variable v₂ on S₂:
-- for each index i, the attribute v₁[i] on S₁ maps to v₂[i] on S₂.
-- This requires the variables to have the same number of attributes.
structure TranslationTask (S₁ S₂ : Type) where
  source : Variable S₁
  target : Variable S₂
  same_size : source.attrs.length = target.attrs.length

-- The individual translation task at index i:
-- maps (v₁[i], blank) → (v₁[i], v₂[i]) on S₁ × S₂.
def TranslationTask.taskAt {S₁ S₂ : Type}
    (tr : TranslationTask S₁ S₂)
    (blank₂ : Attribute S₂)
    (i : Fin tr.source.attrs.length) : Task (S₁ × S₂) where
  input := Attribute.prod (tr.source.attrs.get i) blank₂
  output := Attribute.prod (tr.source.attrs.get i)
    (tr.target.attrs.get ⟨i.val, tr.same_size ▸ i.isLt⟩)

-- Two information variables are `InteroperablePair` if there exist
-- constructors that can translate between them in both directions.
def InteroperablePair {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)] [TaskPossibility (S₂ × S₁)]
    (v₁ : Variable S₁) (v₂ : Variable S₂) : Prop :=
  ∃ (tr₁₂ : TranslationTask S₁ S₂) (tr₂₁ : TranslationTask S₂ S₁),
    tr₁₂.source = v₁ ∧ tr₁₂.target = v₂ ∧
    tr₂₁.source = v₂ ∧ tr₂₁.target = v₁ ∧
    (∃ blank₂ : Attribute S₂, ∀ i : Fin tr₁₂.source.attrs.length,
      Possible (tr₁₂.taskAt blank₂ i)) ∧
    (∃ blank₁ : Attribute S₁, ∀ i : Fin tr₂₁.source.attrs.length,
      Possible (tr₂₁.taskAt blank₁ i))

-- A variable is self-interoperable: it can be translated to itself.
-- This is closely related to being a computation variable.
def SelfInteroperable {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  ∃ blank : Attribute S, ∀ i j : Fin v.attrs.length,
    Possible { input := Attribute.prod (v.attrs.get i) blank,
               output := Attribute.prod (v.attrs.get i) (v.attrs.get j) : Task (S × S) }

-- An information variable can clone each attribute to a blank.
-- This is the diagonal case of self-interoperability: (a_i, blank) → (a_i, a_i).
theorem IsInformationVariable.clone_to_self {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsInformationVariable v) :
    ∃ blank : Attribute S, ∀ i : Fin v.attrs.length,
      Possible { input := Attribute.prod (v.attrs.get i) blank,
                 output := Attribute.prod (v.attrs.get i) (v.attrs.get i) : Task (S × S) } := by
  obtain ⟨_, blank, hclone⟩ := hv
  exact ⟨blank, hclone⟩

end ConstructorTheory
