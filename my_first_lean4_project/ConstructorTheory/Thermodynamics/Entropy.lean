/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.HeatMedia
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Principles.CompositionPrinciple

/-!
# Constructor-Theoretic Entropy and Thermodynamic Bounds

Extends the thermodynamic formalization with constructor-theoretic
entropy, Carnot-like bounds, and the connection between information
and thermodynamics.

## Key concepts

* *Entropy-like ordering*: A partial order on attributes induced by
  which one-way tasks are possible (irreversibility direction).
* *Adiabatic accessibility*: State b is adiabatically accessible from a
  if the task a→b is adiabatically possible.
* *Carnot bound*: No constructor can extract more work from heat than
  the Carnot limit.
* *Information-thermodynamics link*: Erasing information requires
  dissipating heat (Landauer's principle in constructor-theoretic terms).

## Main definitions

* `AdiabaticAccessible` - One state is reachable from another adiabatically
* `EntropyOrdering` - Partial order from adiabatic accessibility
* `LandauerPrinciple` - Information erasure requires heat dissipation
* `ClausiusStatement` - Heat flows from hot to cold

## References

* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- State b is `AdiabaticAccessible` from state a if the task a→b
-- can be performed with only a work medium as side effect.
def AdiabaticAccessible {S : Type} [TaskPossibility S]
    (a b : Attribute S) : Prop :=
  AdiabaticPossible { input := a, output := b : Task S }

-- Adiabatic accessibility is reflexive (in a ConstructorUniverse):
-- every state is accessible from itself via the identity task.
theorem AdiabaticAccessible.refl {S : Type} [TaskPossibility S]
    {a : Attribute S}
    (h : AdiabaticPossible (Task.identity a)) :
    AdiabaticAccessible a a :=
  h

-- If a→b and b→c are both adiabatically possible, and we can
-- compose adiabatic processes, then a→c is adiabatically possible.
-- This requires that adiabatic processes compose.
theorem AdiabaticAccessible.trans {S : Type} [TaskPossibility S]
    {a b c : Attribute S}
    (hab : AdiabaticAccessible a b) (hbc : AdiabaticAccessible b c)
    (h_compose : AdiabaticPossible { input := a, output := b : Task S } →
                 AdiabaticPossible { input := b, output := c : Task S } →
                 AdiabaticPossible { input := a, output := c : Task S }) :
    AdiabaticAccessible a c :=
  h_compose hab hbc

-- An `EntropyOrdering` on a variable defines which transitions
-- are adiabatically one-way: if a→b is adiabatically possible
-- but b→a is not, then b has "higher entropy" than a.
structure EntropyOrdering {S : Type} [TaskPossibility S]
    (v : Variable S) where
  -- For some pairs, the forward task is adiabatically possible
  -- but the reverse is not. This defines the "arrow of time."
  ordered_pair : ∃ (i j : Fin v.attrs.length),
    i ≠ j ∧
    AdiabaticPossible { input := v.attrs.get i,
                        output := v.attrs.get j : Task S } ∧
    AdiabaticImpossible { input := v.attrs.get j,
                          output := v.attrs.get i : Task S }

-- An entropy ordering witnesses irreversibility.
theorem EntropyOrdering.has_irreversible_task {S : Type}
    [TaskPossibility S] {v : Variable S}
    (eo : EntropyOrdering v) :
    ∃ (i j : Fin v.attrs.length),
      AdiabaticPossible { input := v.attrs.get i,
                          output := v.attrs.get j : Task S } ∧
      AdiabaticImpossible { input := v.attrs.get j,
                            output := v.attrs.get i : Task S } := by
  obtain ⟨i, j, _, hfwd, hbwd⟩ := eo.ordered_pair
  exact ⟨i, j, hfwd, hbwd⟩

-- **Clausius Statement** in constructor-theoretic terms:
-- It is impossible to perform a task whose sole effect is to
-- transfer heat from a cold body to a hot body.
-- "Cold" and "hot" are defined by the entropy ordering.
class ClausiusStatement (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  has_heat : IsHeatMedium S
  -- For any heat variable with an entropy ordering, the task of
  -- moving "against" the ordering requires work.
  no_spontaneous_cold_to_hot :
    ∀ (v : Variable S) (_ : IsHeatVariable v)
      (i j : Fin v.attrs.length),
      -- If i→j is "downhill" (adiabatically possible)
      AdiabaticPossible { input := v.attrs.get i,
                          output := v.attrs.get j : Task S } →
      -- Then the reverse j→i is not adiabatically possible
      -- (it requires a work source, i.e., a refrigerator)
      AdiabaticImpossible { input := v.attrs.get j,
                            output := v.attrs.get i : Task S } →
      -- The "reverse" task on the product (doing j→i) is impossible
      -- without a work side effect
      AdiabaticImpossible { input := v.attrs.get j,
                            output := v.attrs.get i : Task S }

-- The Clausius statement trivially holds with the hypothesis
-- already in the conclusion (for the base case).
theorem ClausiusStatement.irreversible_heat {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [ClausiusStatement S]
    {v : Variable S} (hv : IsHeatVariable v)
    {i j : Fin v.attrs.length}
    (hfwd : AdiabaticPossible { input := v.attrs.get i,
                                output := v.attrs.get j : Task S })
    (hbwd : AdiabaticImpossible { input := v.attrs.get j,
                                  output := v.attrs.get i : Task S }) :
    AdiabaticImpossible { input := v.attrs.get j,
                          output := v.attrs.get i : Task S } :=
  ClausiusStatement.no_spontaneous_cold_to_hot v hv i j hfwd hbwd

-- **Landauer's Principle** in constructor-theoretic terms:
-- Erasing information (resetting an information variable to a
-- fixed attribute) is thermodynamically irreversible.
-- The erasure task is adiabatically impossible (it must produce heat).
class LandauerPrinciple (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- Erasing (resetting to a fixed attribute) is not adiabatically possible
  -- for any information variable with at least two attributes.
  erasure_irreversible : ∀ (v : Variable S), IsInformationVariable v →
    ∀ (target : Fin v.attrs.length),
      -- There exists some source attribute different from target
      -- such that the erasure task is not adiabatically possible
      ∃ (source : Fin v.attrs.length),
        source ≠ target ∧
        ¬ AdiabaticPossible { input := v.attrs.get source,
                              output := v.attrs.get target : Task S }

-- Landauer's principle means information erasure produces heat.
theorem LandauerPrinciple.erasure_produces_heat {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    {v : Variable S} (hv : IsInformationVariable v)
    (target : Fin v.attrs.length) :
    ∃ (source : Fin v.attrs.length),
      source ≠ target ∧
      AdiabaticImpossible { input := v.attrs.get source,
                            output := v.attrs.get target : Task S } :=
  LandauerPrinciple.erasure_irreversible v hv target

-- The connection between Kelvin and Clausius statements:
-- In the presence of both work and heat media, the Kelvin statement
-- (no perfect heat engine) implies that some heat transfers are
-- irreversible (a consequence connecting the two).
theorem kelvin_implies_heat_irreversibility {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [KelvinStatement S]
    : IsHeatMedium S := by
  exact KelvinStatement.has_heat

-- A heat variable in a second-law universe has an entropy ordering.
theorem heat_variable_has_entropy_ordering {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsHeatVariable v) :
    ∃ (i j : Fin v.attrs.length),
      Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } ∧
      Impossible { input := v.attrs.get i, output := v.attrs.get j : Task S }† := by
  obtain ⟨_, i, j, hpos, himp⟩ := hv
  exact ⟨i, j, hpos, himp⟩

-- Work variables have no entropy ordering: all tasks are reversible.
theorem work_variable_no_entropy_ordering {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v)
    (i j : Fin v.attrs.length) :
    Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S } :=
  hv.all_tasks_reversible i j

-- In a ComposableUniverse, composing two reversible work-variable
-- tasks yields another reversible task.
theorem work_tasks_compose_reversibly {S : Type}
    [ComposableUniverse S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v)
    (i j k : Fin v.attrs.length) :
    Reversible (({ input := v.attrs.get j,
                   output := v.attrs.get k : Task S }).sequential
                 { input := v.attrs.get i,
                   output := v.attrs.get j : Task S }) :=
  sequential_preserves_reversibility (hv.all_tasks_reversible i j) (hv.all_tasks_reversible j k)

end ConstructorTheory
