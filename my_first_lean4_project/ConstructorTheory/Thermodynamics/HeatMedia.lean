/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Thermodynamics.Basic

/-!
# Heat Variables and Heat Media

Defines heat variables and heat media, following Marletto (2016).

A *heat variable* is an information variable that is NOT a work variable:
some tasks between its attributes are irreversible. This captures the
thermodynamic concept of "heat" — energy that cannot be fully converted
to work.

## Main definitions

* `IsHeatVariable` - An information variable with at least one irreversible task
* `IsHeatMedium` - A substrate with at least one heat variable

## Key results

* `heat_not_work` - A heat variable is not a work variable
* `IsHeatMedium.toInformationMedium` - A heat medium is an information medium

## References

* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
-/

namespace ConstructorTheory

-- A `HeatVariable` is an information variable where at least one
-- pairwise task is irreversible (its transpose is impossible).
-- This is the formal counterpart of "heat" in constructor theory:
-- some transitions can occur but cannot be undone.
def IsHeatVariable {S : Type} [TaskPossibility S] [TaskPossibility (S × S)]
    (v : Variable S) : Prop :=
  IsInformationVariable v ∧
  ∃ i j : Fin v.attrs.length,
    Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } ∧
    Impossible { input := v.attrs.get i, output := v.attrs.get j : Task S }†

-- A heat variable is an information variable.
theorem IsHeatVariable.toInformationVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsHeatVariable v) :
    IsInformationVariable v :=
  h.1

-- A heat variable is NOT a work variable.
-- This is a key result: heat and work are mutually exclusive
-- characterizations of information variables.
theorem heat_not_work {S : Type} [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsHeatVariable v) :
    ¬ IsWorkVariable v := by
  intro hw
  obtain ⟨_, i, j, _, himp⟩ := h
  have hrev := hw.2 i j
  exact himp hrev.2

-- A substrate is a `HeatMedium` if it has at least one heat variable.
def IsHeatMedium (S : Type) [TaskPossibility S] [TaskPossibility (S × S)] : Prop :=
  ∃ v : Variable S, IsHeatVariable v

-- A heat medium is an information medium.
theorem IsHeatMedium.toInformationMedium {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsHeatMedium S) : IsInformationMedium S :=
  let ⟨v, hv⟩ := h
  ⟨v, hv.toInformationVariable⟩

-- A substrate can be both a work medium and a heat medium
-- (it just needs different variables for each).
-- This captures real physical systems like a gas, which has
-- both work-like (pressure/volume) and heat-like (temperature)
-- degrees of freedom.
def HasWorkAndHeat (S : Type) [TaskPossibility S] [TaskPossibility (S × S)] : Prop :=
  IsWorkMedium S ∧ IsHeatMedium S

end ConstructorTheory
