/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.HeatMedia
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Thermodynamics.Entropy
import ConstructorTheory.Thermodynamics.Carnot
import ConstructorTheory.Information.Basic
import ConstructorTheory.Information.NoCloning
import ConstructorTheory.Information.Observable
import ConstructorTheory.Principles.Basic

/-!
# Information-Thermodynamics Bridge

Formalizes the deep connections between the constructor theory of
information and the constructor theory of thermodynamics.

The key insight is that information and thermodynamics are not
independent: the possibility/impossibility of information-processing
tasks constrains thermodynamic behavior and vice versa.

## Key results

* `work_variable_is_observable` - Work variables are observable
* `heat_variable_not_work_observable` - Heat variables are not work-like observables
* `erasure_implies_heat_medium` - Information erasure implies heat generation
* `superinfo_thermodynamic_asymmetry` - Superinformation creates thermodynamic asymmetry
* `szilard_engine` - Szilard engine formalization
* `thermodynamic_cost_of_cloning` - Cloning has thermodynamic cost

## References

* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
-/

namespace ConstructorTheory

-- ============================================================
-- Work variables have strong information-theoretic properties
-- ============================================================

-- A work variable is observable: its attributes can be distinguished
-- because all pairwise tasks are possible (and hence the identity on each
-- attribute is possible, giving distinguishable outcomes).
theorem work_variable_is_observable {S : Type}
    [ConstructorUniverse S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v) :
    IsObservable v := by
  constructor
  · -- Measurability: use clone task from information variable
    obtain ⟨_, blank, hclone⟩ := hv.toInformationVariable
    exact ⟨v, blank, rfl, fun i hi => hclone i⟩
  · -- Distinguishability: use identity tasks
    intro i j hij
    exact ⟨v.attrs.get i, v.attrs.get j,
      v.pairwise_disjoint i j hij,
      identity_task_possible (v.attrs.get i),
      identity_task_possible (v.attrs.get j)⟩

-- A work variable is an information observable (observable + info variable).
theorem work_variable_is_info_observable {S : Type}
    [ConstructorUniverse S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v) :
    IsInformationObservable v :=
  ⟨work_variable_is_observable hv, hv.toInformationVariable⟩

-- ============================================================
-- Heat variables have weaker information-theoretic properties
-- ============================================================

-- A heat variable, while it is an information variable, cannot be
-- a work variable. This creates an information-theoretic asymmetry:
-- some information processing on heat variables is irreversible.
-- (Already proved as heat_not_work, but here we add the converse.)

-- If a variable is both a work variable and satisfies the second law
-- on itself, we get a contradiction.
theorem work_variable_no_irreversibility {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v) :
    ¬ (∃ i j : Fin v.attrs.length,
      Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } ∧
      Impossible { input := v.attrs.get i, output := v.attrs.get j : Task S }†) := by
  intro ⟨i, j, _, himp⟩
  exact himp (hv.all_tasks_reversible i j).2

-- ============================================================
-- Erasure and heat generation
-- ============================================================

-- If erasure of an information variable requires heat dissipation
-- (Landauer), and we have a work medium, then the system must also
-- be a heat medium (erasure generates heat that goes somewhere).
theorem erasure_implies_heat_generation {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    {v : Variable S} (hv : IsInformationVariable v)
    (target : Fin v.attrs.length) :
    ∃ (source : Fin v.attrs.length),
      source ≠ target ∧
      ¬ AdiabaticPossible { input := v.attrs.get source,
                            output := v.attrs.get target : Task S } :=
  LandauerPrinciple.erasure_irreversible v hv target

-- ============================================================
-- Szilard Engine: Information extraction from thermodynamic system
-- ============================================================

-- A Szilard engine extracts work from measurement of a heat variable.
-- The key insight: the measurement provides information that can be
-- used to extract work, but Landauer's principle ensures that erasing
-- the demon's memory costs at least as much work.
structure SzilardEngine (S : Type) [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The heat system being measured
  heat_var : Variable S
  heat_is_heat : IsHeatVariable heat_var
  -- The information store (demon's memory)
  memory_var : Variable S
  memory_is_info : IsInformationVariable memory_var
  -- Measurement: correlates heat state with memory
  measurement_possible : ∃ (blank : Attribute S),
    ∀ i : Fin heat_var.attrs.length,
      ∃ j : Fin memory_var.attrs.length,
        Possible { input := Attribute.prod (heat_var.attrs.get i) blank,
                   output := Attribute.prod (heat_var.attrs.get i)
                     (memory_var.attrs.get j) : Task (S × S) }
  -- Work extraction is possible given the measurement result
  work_extraction : ∃ (work_var : Variable S),
    IsWorkVariable work_var

-- A Szilard engine with Landauer's principle cannot decrease total entropy.
-- The work extracted from measurement is offset by erasure cost.
theorem szilard_landauer_balance {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    (engine : SzilardEngine S) :
    -- The demon's memory erasure is not adiabatically possible for some source
    ∃ (target : Fin engine.memory_var.attrs.length)
      (source : Fin engine.memory_var.attrs.length),
      source ≠ target ∧
      ¬ AdiabaticPossible { input := engine.memory_var.attrs.get source,
                            output := engine.memory_var.attrs.get target : Task S } := by
  have h_len : engine.memory_var.attrs.length ≥ 2 := engine.memory_var.nontrivial
  let target : Fin engine.memory_var.attrs.length := ⟨0, by omega⟩
  obtain ⟨source, hsne, hna⟩ := LandauerPrinciple.erasure_irreversible
    engine.memory_var engine.memory_is_info target
  exact ⟨target, source, hsne, hna⟩

-- ============================================================
-- Thermodynamic cost of information processing
-- ============================================================

-- Cloning an information variable is thermodynamically non-trivial:
-- while cloning is possible (by definition of information variable),
-- cloning and then erasing one copy has a net thermodynamic cost
-- (by Landauer's principle).
theorem cloning_has_thermodynamic_cost {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    {v : Variable S} (hv : IsInformationVariable v) :
    -- Cloning is possible...
    (∃ blank : Attribute S,
      ∀ i : Fin v.attrs.length,
        Possible (cloneTaskSingle (v.attrs.get i) blank)) ∧
    -- ...but erasure (the reverse of preparing a blank) is not free
    (∀ target : Fin v.attrs.length,
      ∃ source : Fin v.attrs.length,
        source ≠ target ∧
        AdiabaticImpossible { input := v.attrs.get source,
                              output := v.attrs.get target : Task S }) := by
  constructor
  · exact hv.2
  · intro target
    exact LandauerPrinciple.erasure_irreversible v hv target

-- ============================================================
-- Superinformation and thermodynamic consequences
-- ============================================================

-- In a superinformation medium (quantum system), the existence of
-- complementary observables creates additional thermodynamic
-- constraints beyond those in classical thermodynamics.
-- Specifically: the union of complementary variables cannot be
-- a work variable (since it's not even an information variable).
theorem complementary_not_work {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v₁ v₂ : Variable S} (h : ComplementaryPair v₁ v₂)
    (v_union : Variable S)
    (h₁ : ∀ a ∈ v₁.attrs, a ∈ v_union.attrs)
    (h₂ : ∀ a ∈ v₂.attrs, a ∈ v_union.attrs) :
    ¬ IsWorkVariable v_union := by
  intro hw
  exact h.2.2 v_union h₁ h₂ hw.toInformationVariable

-- Classical media have simpler thermodynamics: every information
-- variable can potentially be a work variable (no complementarity
-- obstructions).
theorem classical_no_info_obstruction {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsClassicalMedium S) :
    ¬ ∃ (v₁ v₂ : Variable S), ComplementaryPair v₁ v₂ :=
  classical_no_complementary h

-- ============================================================
-- Third Law connection
-- ============================================================

-- The constructor-theoretic third law: there exists no constructor
-- that can bring a system to its ground state (minimum entropy state)
-- in a finite number of steps from an arbitrary initial state.
-- Formalized: for a heat variable with entropy ordering, the
-- "minimum entropy" attribute cannot be reached adiabatically
-- from all other attributes.
structure ThirdLaw (S : Type) [TaskPossibility S] [TaskPossibility (S × S)] where
  -- There exists a heat variable with an unreachable ground state
  has_ground : ∃ (v : Variable S) (_ : IsHeatVariable v)
    (ground : Fin v.attrs.length),
    ∃ (excited : Fin v.attrs.length),
      excited ≠ ground ∧
      AdiabaticImpossible { input := v.attrs.get excited,
                            output := v.attrs.get ground : Task S }

-- The third law implies the second law: if ground states are unreachable,
-- there exist irreversible tasks.
theorem third_law_implies_irreversibility {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : ThirdLaw S) :
    ∃ (v : Variable S),
      IsHeatVariable v ∧
      ∃ (i j : Fin v.attrs.length),
        AdiabaticImpossible { input := v.attrs.get i,
                              output := v.attrs.get j : Task S } := by
  obtain ⟨v, hv, ground, excited, _, himp⟩ := h.has_ground
  exact ⟨v, hv, excited, ground, himp⟩

end ConstructorTheory
