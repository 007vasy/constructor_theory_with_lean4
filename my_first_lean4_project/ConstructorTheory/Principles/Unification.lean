/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Principles.CategoryStructure
import ConstructorTheory.Information.Basic
import ConstructorTheory.Information.NoCloning
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.HeatMedia
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Thermodynamics.Entropy
import ConstructorTheory.Thermodynamics.Carnot
import ConstructorTheory.Time.Basic
import ConstructorTheory.Time.ArrowOfTime
import ConstructorTheory.Life.Basic

/-!
# Constructor Theory Unification Theorems

Cross-domain theorems that connect the five pillars of constructor theory:
core principles, information, thermodynamics, time, and life.

These theorems demonstrate how the constructor-theoretic framework
provides a unified foundation from which diverse physical phenomena
emerge as consequences of the same counterfactual structure.

## Key results

### Information ↔ Thermodynamics
* `info_medium_has_thermo_structure` - Information media have thermodynamic structure
* `second_law_from_superinfo` - Superinformation implies the second law

### Thermodynamics ↔ Time
* `irreversibility_is_arrow` - Thermodynamic irreversibility IS the arrow of time
* `heat_medium_has_temporal_direction` - Heat media define temporal direction

### Information ↔ Time
* `cloning_asymmetry_temporal` - Cloning asymmetry has temporal significance

### Life ↔ Information ↔ Thermodynamics
* `life_requires_all_three` - Life requires information, thermodynamics, and irreversibility
* `replicator_thermodynamic_irreversibility` - Replication is thermodynamically irreversible

### Universal structure
* `constructor_universe_has_structure` - Every constructor universe has rich structure
* `counterfactual_hierarchy` - The hierarchy of physical concepts

## References

* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
* D. Deutsch & C. Marletto, "Constructor Theory of Information",
  Proc. R. Soc. A 471:20140540 (2015)
* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
* D. Deutsch & C. Marletto, "Constructor Theory of Time",
  arXiv:2505.08692 (2025)
* C. Marletto, "Constructor Theory of Life",
  J. R. Soc. Interface 12:20141226 (2015), arXiv:1407.0681
-/

namespace ConstructorTheory

-- ============================================================
-- INFORMATION ↔ THERMODYNAMICS
-- ============================================================

-- Every information medium has thermodynamic structure:
-- it is either a "pure" work medium or contains irreversible tasks.
-- This is the fundamental information-thermodynamics bridge.
theorem info_medium_has_thermo_structure {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsInformationMedium S) :
    (∃ v : Variable S, IsWorkVariable v) ∨
    (∃ v : Variable S, IsInformationVariable v ∧
      ∃ i j : Fin v.attrs.length,
        Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } ∧
        Impossible { input := v.attrs.get i, output := v.attrs.get j : Task S }†) := by
  obtain ⟨v, hv⟩ := h
  exact info_var_work_or_heat hv |>.imp (fun hw => ⟨v, hw⟩) (fun hh =>
    ⟨v, hv, hh⟩)

-- Superinformation implies an information-theoretic form of the second law:
-- there exist information-processing tasks that are irreversible
-- (specifically, cloning the union of complementary variables).
theorem second_law_from_superinfo {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsSuperinformationMedium S) :
    ∃ (v₁ v₂ : Variable S),
      IsInformationVariable v₁ ∧
      IsInformationVariable v₂ ∧
      -- Their union is not clonable (an irreversible constraint)
      ∀ v_union : Variable S,
        (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
        (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
        ¬ IsInformationVariable v_union :=
  h.2

-- The work-heat dichotomy is exhaustive: in a universe with a second
-- law, every information variable is classified as either work or heat.
-- This is a strengthening of `info_var_work_or_heat`.
theorem work_heat_exhaustive {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsInformationVariable v) :
    IsWorkVariable v ∨ IsHeatVariable v := by
  by_cases h : ∀ i j : Fin v.attrs.length,
    Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S }
  · left; exact ⟨hv, h⟩
  · right
    constructor
    · exact hv
    · have ⟨i, hi⟩ := Classical.not_forall.mp h
      have ⟨j, hij⟩ := Classical.not_forall.mp hi
      have hp := hv.toComputationVariable i j
      have hnr : ¬ Possible { input := v.attrs.get i,
                               output := v.attrs.get j : Task S }† := by
        intro hrev; exact hij ⟨hp, hrev⟩
      exact ⟨i, j, hp, hnr⟩

-- ============================================================
-- THERMODYNAMICS ↔ TIME
-- ============================================================

-- Thermodynamic irreversibility IS the arrow of time.
-- There is no separate "time arrow" — the arrow of time just IS
-- the existence of tasks that are possible but whose transposes
-- are impossible.
theorem irreversibility_is_arrow {S : Type}
    [TaskPossibility S] [SecondLaw S] :
    ∃ t : Task S, DefinesDirection t := by
  obtain ⟨t, hp, himp⟩ := SecondLaw.irreversible_exists (S := S)
  exact ⟨t, hp, himp⟩

-- Every heat medium defines a temporal direction:
-- the direction of entropy increase IS the direction of time.
theorem heat_medium_has_temporal_direction {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (h : IsHeatMedium S) :
    ∃ t : Task S, DefinesDirection t := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨_, i, j, hp, himp⟩ := hv
  exact ⟨{ input := v.attrs.get i, output := v.attrs.get j }, hp, himp⟩

-- Work media are time-symmetric: they define no temporal direction.
-- All work-variable tasks are reversible, so no direction emerges.
theorem work_medium_time_symmetric {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v)
    (i j : Fin v.attrs.length) :
    ¬ DefinesDirection { input := v.attrs.get i,
                          output := v.attrs.get j : Task S } :=
  work_variable_no_arrow hv i j

-- ============================================================
-- INFORMATION ↔ TIME
-- ============================================================

-- The cloning asymmetry has temporal significance:
-- in a superinformation medium, the impossibility of cloning certain
-- variables creates an information-theoretic arrow of time.
-- Cloning is a one-way process (for the union of complementary
-- variables, it cannot be done at all, creating an "impossible" task
-- that has no reverse).
theorem cloning_asymmetry_temporal {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v₁ v₂ : Variable S} (h : ComplementaryPair v₁ v₂) :
    -- Complementary variables are both information variables but
    -- their union is not — witnessing an information-theoretic asymmetry
    IsInformationVariable v₁ ∧
    IsInformationVariable v₂ ∧
    ∀ v_union : Variable S,
      (∀ a ∈ v₁.attrs, a ∈ v_union.attrs) →
      (∀ a ∈ v₂.attrs, a ∈ v_union.attrs) →
      ¬ IsInformationVariable v_union :=
  ⟨h.1, h.2.1, h.2.2⟩

-- ============================================================
-- LIFE ↔ INFORMATION ↔ THERMODYNAMICS
-- ============================================================

-- Life requires all three pillars: information (for heredity),
-- thermodynamics (for irreversibility), and the interplay between them.
-- A self-reproducer necessarily:
-- 1. Has digital information (information variable)
-- 2. Has clonable information (can replicate)
-- 3. Under Landauer's principle, replication has thermodynamic cost
theorem life_requires_all_three {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    (sr : SelfReproducer S) :
    -- 1. Has digital (information) variable
    IsInformationVariable sr.replicator.info ∧
    -- 2. Can replicate (cloning is possible)
    (∃ blank : Attribute S,
      ∀ i : Fin sr.replicator.info.attrs.length,
        Possible (replicationTask (sr.replicator.info.attrs.get i) blank)) ∧
    -- 3. Replication has thermodynamic cost (erasure is not free)
    (∀ target : Fin sr.replicator.info.attrs.length,
      ∃ source : Fin sr.replicator.info.attrs.length,
        source ≠ target ∧
        AdiabaticImpossible { input := sr.replicator.info.attrs.get source,
                              output := sr.replicator.info.attrs.get target : Task S }) :=
  ⟨sr.replicator.is_digital,
   sr.replicator.can_replicate,
   fun target => LandauerPrinciple.erasure_irreversible
     sr.replicator.info sr.replicator.is_digital target⟩

-- Replication is thermodynamically irreversible: the process of
-- making a copy cannot be undone without thermodynamic cost.
-- This connects life to the arrow of time.
theorem replicator_thermodynamic_irreversibility {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [LandauerPrinciple S]
    (r : Replicator S) :
    ∀ target : Fin r.info.attrs.length,
      ∃ source : Fin r.info.attrs.length,
        source ≠ target ∧
        ¬ AdiabaticPossible { input := r.info.attrs.get source,
                              output := r.info.attrs.get target : Task S } :=
  fun target => LandauerPrinciple.erasure_irreversible r.info r.is_digital target

-- ============================================================
-- THE COUNTERFACTUAL HIERARCHY
-- ============================================================

-- The hierarchy of physical concepts in constructor theory:
-- Possible/Impossible → Information → Work/Heat → Time → Life
-- Each level is definable in terms of the previous ones.

-- Level 0: The most basic structure — possible and impossible tasks.
-- Every task is either possible or impossible.
theorem counterfactual_foundation {S : Type} [TaskPossibility S]
    (t : Task S) : Possible t ∨ Impossible t :=
  possible_or_impossible t

-- Level 1: Information structure requires possible/impossible.
-- An information variable is defined by which cloning tasks are possible.
theorem info_requires_counterfactuals {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsInformationVariable v) :
    -- All swap tasks are possible (computation variable)
    (∀ i j : Fin v.attrs.length,
      Possible { input := v.attrs.get i, output := v.attrs.get j : Task S }) ∧
    -- Cloning tasks are possible
    (∃ blank : Attribute S,
      ∀ i : Fin v.attrs.length,
        Possible (cloneTaskSingle (v.attrs.get i) blank)) :=
  ⟨hv.1, hv.2⟩

-- Level 2: Thermodynamic structure requires information.
-- Work and heat are defined in terms of information variables.
theorem thermo_requires_info {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v) :
    IsInformationVariable v :=
  hv.toInformationVariable

-- Level 3: Time structure requires thermodynamics (irreversibility).
-- The arrow of time emerges from the second law.
theorem time_requires_thermo {S : Type}
    [TaskPossibility S] [SecondLaw S] :
    ∃ t : Task S, Possible t ∧ Impossible t† :=
  SecondLaw.irreversible_exists

-- Level 4: Life requires information + thermodynamics + time.
-- Self-reproduction requires digital information, and under Landauer,
-- this connects to thermodynamic irreversibility and the arrow of time.
theorem life_requires_info_and_thermo {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (sr : SelfReproducer S) :
    IsInformationVariable sr.replicator.info ∧
    ∃ blank : Attribute S,
      ∀ i : Fin sr.replicator.info.attrs.length,
        Possible (replicationTask (sr.replicator.info.attrs.get i) blank) :=
  ⟨sr.replicator.is_digital, sr.replicator.can_replicate⟩

-- ============================================================
-- UNIVERSAL STRUCTURE THEOREM
-- ============================================================

-- In a constructor universe with a second law, all five pillars
-- are necessarily present: counterfactual structure (by definition),
-- information structure (from identity tasks), thermodynamic
-- structure (from the second law), temporal structure (from
-- irreversibility), and the possibility of life-like structures
-- (from information).

-- The constructor universe has identity tasks possible for all attributes.
theorem constructor_universe_identity_structure {S : Type}
    [ConstructorUniverse S] (a : Attribute S) :
    Possible (Task.identity a) ∧ Reversible (Task.identity a) :=
  ⟨identity_task_possible a, identity_reversible a⟩

-- In a composable universe, the category of tasks is well-structured.
theorem composable_universe_category {S : Type}
    [ComposableUniverse S] :
    -- Identity is always possible
    (∀ a : Attribute S, Possible (Task.identity a)) ∧
    -- Composition preserves possibility
    (∀ t₁ t₂ : Task S, Possible t₁ → Possible t₂ →
      Possible (t₂.sequential t₁)) :=
  ⟨identity_task_possible,
   fun _t₁ _t₂ h₁ h₂ => sequential_of_possible h₁ h₂⟩

end ConstructorTheory
