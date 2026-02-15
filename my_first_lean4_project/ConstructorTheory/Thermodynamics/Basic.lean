/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Possible
import ConstructorTheory.Composition
import ConstructorTheory.Information.Basic

/-!
# Constructor Theory of Thermodynamics: Foundations

Defines the constructor-theoretic formulation of thermodynamics following
Marletto (2016). The key insight is that thermodynamic concepts like
"work" and "heat" are defined in terms of which tasks are possible
and which are impossible, rather than through dynamical laws.

## Key concepts

* *Adiabatic possibility*: A task is adiabatically possible if it can be
  performed with only a work medium as a side effect.
* *Work variable*: An information variable where all tasks between its
  attributes are reversible (can be undone without leaving any trace).
* *Work medium*: A substrate that has at least one work variable.

## Main definitions

* `AdiabaticPossible` - A task that is possible with a work-medium side effect
* `AdiabaticImpossible` - A task that is not adiabatically possible
* `IsWorkVariable` - An information variable with all pairwise tasks reversible
* `IsWorkMedium` - A substrate with at least one work variable

## References

* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
-/

namespace ConstructorTheory

-- A task is `AdiabaticPossible` if it can be performed by a constructor
-- that uses only a work medium as an ancilla.
-- Following Marletto (2016), adiabatic possibility captures "mechanical"
-- processes that leave no thermodynamic trace.
-- We define this abstractly: there exists a work-like side-system
-- and a possible composite task.
def AdiabaticPossible {S : Type} [TaskPossibility S] (t : Task S) : Prop :=
  ∃ (W : Type) (instW : TaskPossibility W) (instSW : TaskPossibility (S × W))
    (tw : Task W),
    @Reversible W instW tw ∧
    @Possible (S × W) instSW (t ⊗ tw)

-- A task is `AdiabaticImpossible` if it is not adiabatically possible.
def AdiabaticImpossible {S : Type} [TaskPossibility S] (t : Task S) : Prop :=
  ¬ AdiabaticPossible t

-- A `WorkVariable` is an information variable where every pairwise
-- task between its attributes is reversible.
-- This captures the intuition that "work" can always be extracted
-- and restored without any thermodynamic cost.
def IsWorkVariable {S : Type} [TaskPossibility S] [TaskPossibility (S × S)]
    (v : Variable S) : Prop :=
  IsInformationVariable v ∧
  ∀ i j : Fin v.attrs.length,
    Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S }

-- A work variable is an information variable.
theorem IsWorkVariable.toInformationVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsWorkVariable v) :
    IsInformationVariable v :=
  h.1

-- A work variable is a computation variable.
theorem IsWorkVariable.toComputationVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsWorkVariable v) :
    IsComputationVariable v :=
  h.1.toComputationVariable

-- All tasks in a work variable are possible (follows from reversibility).
theorem IsWorkVariable.all_tasks_possible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsWorkVariable v)
    (i j : Fin v.attrs.length) :
    Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } :=
  (h.2 i j).1

-- All tasks in a work variable have possible transposes.
theorem IsWorkVariable.all_tasks_reversible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsWorkVariable v)
    (i j : Fin v.attrs.length) :
    Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S } :=
  h.2 i j

-- A substrate is a `WorkMedium` if it has at least one work variable.
def IsWorkMedium (S : Type) [TaskPossibility S] [TaskPossibility (S × S)] : Prop :=
  ∃ v : Variable S, IsWorkVariable v

-- A work medium is an information medium.
theorem IsWorkMedium.toInformationMedium {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsWorkMedium S) : IsInformationMedium S :=
  let ⟨v, hv⟩ := h
  ⟨v, hv.toInformationVariable⟩

end ConstructorTheory
