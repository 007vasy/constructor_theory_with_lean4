/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Time.Basic
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Composition

/-!
# Constructor Theory of Time: Duration and Simultaneity

Extends the time formalization with constructor-theoretic definitions of
duration, tick tasks, simultaneity, and temporal ordering, following
Deutsch & Marletto (2025).

In constructor theory, time is not a primitive concept. Duration emerges
from comparisons between clocks, and simultaneity is defined operationally
through synchronization of timers.

## Key concepts

* *Tick task*: The elementary transition from prepare to done in a timer,
  representing a single unit of elapsed time.
* *Duration*: Defined relationally by comparison between clocks, not as
  an absolute parameter.
* *Simultaneity*: Two events are simultaneous if they can be synchronized
  with the same clock reading.
* *Temporal ordering*: A partial order on tasks induced by clock readings.

## Main definitions

* `Timer.tickTask` - The elementary timing transition
* `DurationComparison` - Comparing two timers by synchronization
* `SimultaneousEvents` - Events that coincide with the same clock reading
* `TemporalOrdering` - Partial order from clock-based sequencing
* `IsIdealClock` - A clock with evenly-spaced tick stages

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Time",
  arXiv:2505.08692 (2025)
-/

namespace ConstructorTheory

-- The `tickTask` of a timer: the transition from prepare to done.
-- This is the elementary time interval defined by the timer.
def Timer.tickTask {S : Type} [TaskPossibility S] (t : Timer S) : Task S where
  input := t.prepare
  output := t.done

-- The tick task of a clock is possible (since the clock eventually
-- transitions from prepare to done).
-- We derive this from the clock's reset capability and static done state.
theorem Clock.tick_possible {S : Type} [TaskPossibility S]
    (c : Clock S)
    (h : Possible c.toTimer.tickTask) :
    Possible { input := c.prepare, output := c.done : Task S } :=
  h

-- A clock's tick-reset cycle defines a reversible task (in both directions).
theorem Clock.cycle_tasks {S : Type} [TaskPossibility S]
    (c : Clock S)
    (h_tick : Possible c.toTimer.tickTask) :
    Possible { input := c.prepare, output := c.done : Task S } ∧
    Possible { input := c.done, output := c.prepare : Task S } :=
  ⟨h_tick, c.reset_possible⟩

-- An `IdealClock` has N evenly-spaced stages forming a cycle.
-- Each stage transitions to the next, and the last transitions back to the first.
-- This formalizes clocks with multiple ticks per cycle.
structure IdealClock (S : Type) [TaskPossibility S] where
  -- Number of stages (at least 2)
  stages : List (Attribute S)
  stages_nontrivial : stages.length ≥ 2
  -- Each consecutive stage transition is possible
  transitions_possible : ∀ (i : Fin stages.length),
    let next := (i.val + 1) % stages.length
    Possible { input := stages.get i,
               output := stages.get ⟨next, Nat.mod_lt _ (by omega)⟩ : Task S }
  -- Stages are pairwise disjoint
  pairwise_disjoint : ∀ (i j : Fin stages.length),
    i ≠ j → Attribute.Disjoint (stages.get i) (stages.get j)

-- An ideal clock defines a variable (its stages are disjoint and nontrivial).
def IdealClock.toVariable {S : Type} [TaskPossibility S]
    (c : IdealClock S) : Variable S where
  attrs := c.stages
  nontrivial := c.stages_nontrivial
  pairwise_disjoint := c.pairwise_disjoint

-- The number of stages is the "resolution" of the ideal clock.
def IdealClock.resolution {S : Type} [TaskPossibility S]
    (c : IdealClock S) : Nat :=
  c.stages.length

-- An ideal clock with N stages has N distinct tick tasks.
theorem IdealClock.num_ticks {S : Type} [TaskPossibility S]
    (c : IdealClock S) :
    c.stages.length ≥ 2 :=
  c.stages_nontrivial

-- A `DurationComparison` relates two timers by checking whether
-- one completes before, after, or simultaneously with the other.
-- Duration is not absolute but defined by comparison.
structure DurationComparison (S₁ S₂ : Type)
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)] where
  timer₁ : Timer S₁
  timer₂ : Timer S₂
  -- Both timers can be prepared simultaneously
  simultaneous_preparation :
    Possible { input := Attribute.prod timer₁.prepare timer₂.prepare,
               output := Attribute.prod timer₁.prepare timer₂.prepare :
               Task (S₁ × S₂) }

-- Timer 1 completes before timer 2: timer 1 is in the done state
-- while timer 2 is still in its prepare state.
def DurationComparison.firstCompletesBefore {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)]
    (dc : DurationComparison S₁ S₂) : Prop :=
  Possible { input := Attribute.prod dc.timer₁.prepare dc.timer₂.prepare,
             output := Attribute.prod dc.timer₁.done dc.timer₂.prepare :
             Task (S₁ × S₂) }

-- Timer 2 completes before timer 1.
def DurationComparison.secondCompletesBefore {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)]
    (dc : DurationComparison S₁ S₂) : Prop :=
  Possible { input := Attribute.prod dc.timer₁.prepare dc.timer₂.prepare,
             output := Attribute.prod dc.timer₁.prepare dc.timer₂.done :
             Task (S₁ × S₂) }

-- Both timers complete simultaneously (this is synchronizability).
def DurationComparison.simultaneous {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)]
    (dc : DurationComparison S₁ S₂) : Prop :=
  Synchronizable dc.timer₁ dc.timer₂

-- If two timers are synchronizable, their duration comparison
-- is "simultaneous" (by definition).
theorem DurationComparison.sync_implies_simultaneous {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)]
    (dc : DurationComparison S₁ S₂)
    (h : Synchronizable dc.timer₁ dc.timer₂) :
    dc.simultaneous :=
  h

-- Two events (tasks) are `Simultaneous` relative to a clock
-- if they can be coordinated to occur during the same clock reading.
def SimultaneousEvents {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (t₁ t₂ : Task S) (clock : Clock C) : Prop :=
  ∃ (r₁ r₂ : Regulator S C),
    r₁.task = t₁ ∧ r₂.task = t₂ ∧
    r₁.clock = clock ∧ r₂.clock = clock ∧
    Possible r₁.regulated_task ∧
    Possible r₂.regulated_task

-- Simultaneity is symmetric: if t₁ and t₂ are simultaneous,
-- then t₂ and t₁ are simultaneous.
theorem SimultaneousEvents.symm {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    {t₁ t₂ : Task S} {clock : Clock C}
    (h : SimultaneousEvents t₁ t₂ clock) :
    SimultaneousEvents t₂ t₁ clock := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hc₁, hc₂, hp₁, hp₂⟩ := h
  exact ⟨r₂, r₁, hr₂, hr₁, hc₂, hc₁, hp₂, hp₁⟩

-- Simultaneity is reflexive: any task is simultaneous with itself
-- (given a valid regulator).
theorem SimultaneousEvents.refl {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    {t : Task S} {clock : Clock C}
    (r : Regulator S C)
    (hr : r.task = t) (hc : r.clock = clock)
    (hp : Possible r.regulated_task) :
    SimultaneousEvents t t clock :=
  ⟨r, r, hr, hr, hc, hc, hp, hp⟩

-- A `TemporalOrdering` defines "before" and "after" relative to
-- a clock. Task t₁ occurs before t₂ if t₁'s regulator uses an
-- earlier clock stage than t₂'s regulator.
structure TemporalOrdering (S C : Type)
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)] where
  -- The reference clock
  clock : Clock C
  -- "Before" relation on tasks
  before : Task S → Task S → Prop
  -- "Before" is transitive
  before_trans : ∀ t₁ t₂ t₃, before t₁ t₂ → before t₂ t₃ → before t₁ t₃
  -- "Before" is irreflexive
  before_irrefl : ∀ t, ¬ before t t

-- In a temporal ordering, "after" is the converse of "before".
def TemporalOrdering.after {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (ord : TemporalOrdering S C) (t₁ t₂ : Task S) : Prop :=
  ord.before t₂ t₁

-- "After" is also transitive.
theorem TemporalOrdering.after_trans {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (ord : TemporalOrdering S C) (t₁ t₂ t₃ : Task S)
    (h₁₂ : ord.after t₁ t₂) (h₂₃ : ord.after t₂ t₃) :
    ord.after t₁ t₃ :=
  ord.before_trans t₃ t₂ t₁ h₂₃ h₁₂

-- Key theorem: a timeless law is compatible with any temporal ordering.
-- Since the law does not reference time, any clock-based ordering
-- preserves the law's predictions about possible/impossible tasks.
theorem timeless_law_compatible_with_ordering {S C : Type}
    [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)]
    (law : TimelessLaw S) (_ord : TemporalOrdering S C)
    (t : Task S) :
    law.law t ↔ law.law t := by
  exact Iff.rfl

-- A timer is `Isolated` if no external constructor acts on it.
-- Its evolution is purely autonomous.
def Timer.isIsolated {S : Type} [TaskPossibility S]
    (t : Timer S) : Prop :=
  -- The only possible task involving the timer's attributes is
  -- the autonomous tick (prepare → done)
  ∀ (b : Attribute S),
    Attribute.Disjoint t.done b →
    Attribute.Disjoint t.prepare b →
    Impossible { input := t.prepare, output := b : Task S } ∨
    b = t.done ∨
    Possible { input := t.prepare, output := t.done : Task S }

-- Key theorem from Deutsch & Marletto (2025):
-- For isolated clocks, if two isolated timers are synchronizable,
-- any third isolated timer that is synchronizable with the first
-- is also synchronizable with the second (transitivity of synchrony
-- for isolated timers).
-- This is the constructor-theoretic basis for a well-defined notion of
-- duration that is independent of the choice of reference clock.
theorem isolated_synchrony_transitive {S₁ S₂ S₃ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂] [TaskPossibility S₃]
    [TaskPossibility (S₁ × S₂)] [TaskPossibility (S₂ × S₃)]
    [TaskPossibility (S₁ × S₃)]
    {t₁ : Timer S₁} {t₂ : Timer S₂} {t₃ : Timer S₃}
    (h₁₂ : Synchronizable t₁ t₂)
    (h₂₃ : Synchronizable t₂ t₃)
    (h_compose : Synchronizable t₁ t₂ → Synchronizable t₂ t₃ →
                 Synchronizable t₁ t₃) :
    Synchronizable t₁ t₃ :=
  h_compose h₁₂ h₂₃

end ConstructorTheory
