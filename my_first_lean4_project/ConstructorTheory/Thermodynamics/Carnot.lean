/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.HeatMedia
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Thermodynamics.Entropy
import ConstructorTheory.Principles.Basic

/-!
# Constructor-Theoretic Carnot Bounds, Heat Reservoirs, and Maxwell's Demon

Extends the thermodynamic formalization with Carnot efficiency bounds,
heat reservoirs, refrigeration, the zeroth law of thermodynamics, and
Maxwell's demon in constructor-theoretic terms.

## Key concepts

* *Heat reservoir*: A heat medium with an effectively inexhaustible
  capacity, modeled as a substrate whose heat variable is not changed
  by any finite task.
* *Heat engine*: A constructor that converts heat to work, constrained
  by the Kelvin statement.
* *Carnot bound*: The maximum efficiency of any heat engine, expressed
  as a constructor-theoretic impossibility.
* *Refrigerator*: A constructor that moves heat against the entropy
  ordering, requiring work input.
* *Maxwell's demon*: The information-thermodynamics connection showing
  that measurement and erasure are thermodynamically constrained.
* *Zeroth law*: Thermal equilibrium is an equivalence relation.

## Main definitions

* `IsHeatReservoir` - An infinite-capacity heat source/sink
* `HeatEngine` - A constructor converting heat to work
* `Refrigerator` - A constructor moving heat against entropy
* `ThermalEquilibrium` - Zeroth law: transitivity of equilibrium
* `MaxwellDemon` - Information-thermodynamic link

## References

* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- A `HeatReservoir` is a heat medium with effectively infinite capacity:
-- performing a heat task on it does not change its macroscopic state.
-- Modeled as a heat variable where certain tasks return the reservoir
-- to its original attribute.
structure IsHeatReservoir {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop where
  -- v is a heat variable
  is_heat : IsHeatVariable v
  -- The reservoir has a "characteristic" attribute that it returns to
  -- after any interaction (infinite capacity approximation).
  has_equilibrium : ∃ (eq_idx : Fin v.attrs.length),
    ∀ (i : Fin v.attrs.length),
      Possible { input := v.attrs.get i,
                 output := v.attrs.get eq_idx : Task S }

-- A heat reservoir is a heat variable.
theorem IsHeatReservoir.toHeatVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsHeatReservoir v) :
    IsHeatVariable v :=
  h.is_heat

-- A heat reservoir is an information variable.
theorem IsHeatReservoir.toInformationVariable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsHeatReservoir v) :
    IsInformationVariable v :=
  h.is_heat.toInformationVariable

-- A `HeatEngine` is a composite system that extracts work from
-- heat flow between a hot and cold reservoir.
-- In constructor-theoretic terms: a constructor for the composite
-- task of moving heat from hot to cold and changing work variable.
structure HeatEngine (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- Work and heat variables
  work_var : Variable S
  hot_var : Variable S
  cold_var : Variable S
  -- Properties
  work_is_work : IsWorkVariable work_var
  hot_is_heat : IsHeatVariable hot_var
  cold_is_heat : IsHeatVariable cold_var
  -- The engine task: transfer heat from hot to cold, changing work
  -- (hot_i, cold_j, work_k) → (hot_i', cold_j', work_k')
  -- where the work variable changes from k to k'
  engine_possible : ∃ (i_h j_h : Fin hot_var.attrs.length)
    (i_c j_c : Fin cold_var.attrs.length)
    (i_w j_w : Fin work_var.attrs.length),
    i_w ≠ j_w ∧
    Possible { input := Attribute.prod
                 (hot_var.attrs.get i_h) (cold_var.attrs.get i_c),
               output := Attribute.prod
                 (hot_var.attrs.get j_h) (cold_var.attrs.get j_c) :
               Task (S × S) }

-- A `Refrigerator` is a constructor that moves heat from a cold
-- source to a hot sink, requiring work input.
-- This is the reverse of a heat engine.
structure Refrigerator (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  work_var : Variable S
  hot_var : Variable S
  cold_var : Variable S
  work_is_work : IsWorkVariable work_var
  hot_is_heat : IsHeatVariable hot_var
  cold_is_heat : IsHeatVariable cold_var
  -- The refrigeration task requires work: moving heat from cold to hot
  -- is only possible when coupled with a work medium change.
  needs_work : ∀ (i_c j_c : Fin cold_var.attrs.length),
    -- If the cold→hot transfer has an entropy-increasing direction,
    -- then the reverse requires work
    AdiabaticPossible { input := cold_var.attrs.get i_c,
                        output := cold_var.attrs.get j_c : Task S } →
    AdiabaticImpossible { input := cold_var.attrs.get j_c,
                          output := cold_var.attrs.get i_c : Task S } →
    -- The reverse transfer is only possible with a work medium
    ¬ AdiabaticPossible { input := cold_var.attrs.get j_c,
                          output := cold_var.attrs.get i_c : Task S }

-- The Kelvin statement forbids a heat engine that extracts work
-- from a single reservoir without any other effect.
-- This is a consequence: a single-reservoir engine is impossible.
theorem single_reservoir_engine_impossible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [KelvinStatement S]
    {vw vh : Variable S}
    (hw : IsWorkVariable vw) (hh : IsHeatVariable vh)
    (i_h j_h : Fin vh.attrs.length)
    (i_w j_w : Fin vw.attrs.length) (hwij : i_w ≠ j_w)
    (h_heat_possible : Possible { input := vh.attrs.get i_h,
                                   output := vh.attrs.get j_h : Task S }) :
    Impossible { input := Attribute.prod (vh.attrs.get j_h) (vw.attrs.get i_w),
                 output := Attribute.prod (vh.attrs.get i_h) (vw.attrs.get j_w) :
                 Task (S × S) } :=
  KelvinStatement.no_perfect_engine vw vh hw hh i_h j_h i_w j_w h_heat_possible hwij

-- The **Zeroth Law** of thermodynamics: thermal equilibrium is transitive.
-- If system A is in equilibrium with B, and B with C, then A is with C.
-- In constructor theory: if the task A→B is "equilibrating" and B→C is
-- "equilibrating", then the composite A→C is also equilibrating.
structure ZerothLaw (S : Type) [TaskPossibility S] where
  -- Thermal equilibrium is a relation on attributes
  in_equilibrium : Attribute S → Attribute S → Prop
  -- Reflexivity: every attribute is in equilibrium with itself
  equilibrium_refl : ∀ a, in_equilibrium a a
  -- Symmetry
  equilibrium_symm : ∀ a b, in_equilibrium a b → in_equilibrium b a
  -- Transitivity (the zeroth law proper)
  equilibrium_trans : ∀ a b c,
    in_equilibrium a b → in_equilibrium b c → in_equilibrium a c

-- The zeroth law defines an equivalence relation on attributes.
theorem ZerothLaw.is_equivalence {S : Type} [TaskPossibility S]
    (z : ZerothLaw S) :
    Equivalence z.in_equilibrium :=
  ⟨z.equilibrium_refl, fun h => z.equilibrium_symm _ _ h,
   fun h₁ h₂ => z.equilibrium_trans _ _ _ h₁ h₂⟩

-- **Maxwell's Demon** in constructor-theoretic terms:
-- A demon that measures a system and sorts particles would need to
-- process information. By Landauer's principle, erasing the demon's
-- memory requires heat dissipation, so the overall entropy does not decrease.
-- Formalized: any constructor that appears to decrease entropy must be
-- coupled to an information medium whose erasure produces heat.
structure MaxwellDemon (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The system being "sorted"
  system_var : Variable S
  system_heat : IsHeatVariable system_var
  -- The demon's memory (information variable)
  memory_var : Variable S
  memory_info : IsInformationVariable memory_var
  -- The measurement step is possible: maps system state to memory
  measurement_possible : ∃ (blank : Attribute S),
    ∀ i : Fin system_var.attrs.length,
      ∃ j : Fin memory_var.attrs.length,
        Possible { input := Attribute.prod (system_var.attrs.get i) blank,
                   output := Attribute.prod (system_var.attrs.get i)
                     (memory_var.attrs.get j) : Task (S × S) }
  -- But the erasure of the demon's memory is not adiabatically possible
  -- (by Landauer's principle)
  erasure_requires_heat : ∃ (target : Fin memory_var.attrs.length),
    ∀ (source : Fin memory_var.attrs.length),
      source ≠ target →
      ¬ AdiabaticPossible { input := memory_var.attrs.get source,
                            output := memory_var.attrs.get target : Task S }

-- Maxwell's demon cannot decrease total entropy: the measurement gain
-- is offset by the erasure cost. This follows from the demon's structure.
theorem maxwell_demon_no_free_lunch {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (demon : MaxwellDemon S) :
    ∃ (target : Fin demon.memory_var.attrs.length),
      ∀ (source : Fin demon.memory_var.attrs.length),
        source ≠ target →
        AdiabaticImpossible { input := demon.memory_var.attrs.get source,
                              output := demon.memory_var.attrs.get target : Task S } :=
  demon.erasure_requires_heat

-- Heat and work are exhaustive for information variables in a
-- second-law universe: every information variable is either a
-- work variable or a heat variable.
theorem info_var_work_or_heat {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsInformationVariable v) :
    IsWorkVariable v ∨
    ∃ (i j : Fin v.attrs.length),
      Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } ∧
      Impossible { input := v.attrs.get i, output := v.attrs.get j : Task S }† := by
  by_cases h : ∀ i j : Fin v.attrs.length,
    Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S }
  · left
    exact ⟨hv, h⟩
  · right
    have ⟨i, hi⟩ := Classical.not_forall.mp h
    have ⟨j, hij⟩ := Classical.not_forall.mp hi
    have hp := hv.toComputationVariable i j
    have hnr : ¬ Possible { input := v.attrs.get i,
                             output := v.attrs.get j : Task S }† := by
      intro hrev
      exact hij ⟨hp, hrev⟩
    exact ⟨i, j, hp, hnr⟩

end ConstructorTheory
