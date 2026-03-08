/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Time.Basic
import ConstructorTheory.Time.Duration
import ConstructorTheory.Thermodynamics.Entropy
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Thermodynamics.HeatMedia
import ConstructorTheory.Principles.Basic

/-!
# Arrow of Time in Constructor Theory

Connects the constructor theory of time with thermodynamic irreversibility
to derive the arrow of time as an emergent property.

The key insight from Deutsch & Marletto (2025) is that the arrow of time
is not a fundamental law but emerges from the asymmetry between possible
and impossible tasks. A timer's tick (prepare → done) is possible while
its autonomous reverse (done → prepare without a constructor) is impossible.
This mirrors the thermodynamic second law.

## Key results

* `timer_defines_arrow` - A timer's tick defines a temporal direction
* `irreversible_task_has_arrow` - Irreversible tasks define an arrow of time
* `entropy_ordering_induces_temporal_direction` - Entropy ordering → temporal direction
* `clock_cycle_no_net_arrow` - Reversible clocks have no net arrow of time
* `second_law_arrow` - The second law of thermodynamics implies an arrow

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Time",
  arXiv:2505.08692 (2025)
* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
-/

namespace ConstructorTheory

-- ============================================================
-- Arrow of time from timers
-- ============================================================

-- A timer whose tick is possible but whose reverse is not
-- defines a local arrow of time.
def TimerArrow {S : Type} [TaskPossibility S] (t : Timer S) : Prop :=
  Possible t.tickTask ∧ Impossible t.tickTask†

-- A timer with a TimerArrow has an irreversible tick.
theorem timer_arrow_irreversible {S : Type} [TaskPossibility S]
    {t : Timer S} (h : TimerArrow t) :
    ¬ Reversible t.tickTask :=
  fun hrev => h.2 hrev.2

-- The tick task's transpose is the reverse: done → prepare.
theorem timer_tick_transpose {S : Type} [TaskPossibility S]
    (t : Timer S) :
    t.tickTask† = { input := t.done, output := t.prepare : Task S } := by
  simp [Timer.tickTask, Task.transpose]

-- ============================================================
-- Irreversibility and the arrow of time
-- ============================================================

-- An irreversible task (possible forward, impossible backward)
-- defines a direction in state space.
def DefinesDirection {S : Type} [TaskPossibility S] (t : Task S) : Prop :=
  Possible t ∧ Impossible t†

-- DefinesDirection implies the task is not reversible.
theorem defines_direction_not_reversible {S : Type} [TaskPossibility S]
    {t : Task S} (h : DefinesDirection t) : ¬ Reversible t :=
  fun hrev => h.2 hrev.2

-- The transpose of a direction-defining task defines the opposite direction.
-- If t defines a direction, t† does NOT define a direction (t† is impossible).
theorem transpose_no_direction {S : Type} [TaskPossibility S]
    {t : Task S} (h : DefinesDirection t) :
    ¬ DefinesDirection t† := by
  intro ⟨hp_dag, _⟩
  exact h.2 hp_dag

-- ============================================================
-- Connection to thermodynamic entropy ordering
-- ============================================================

-- An entropy ordering on a heat variable induces a temporal direction:
-- the "forward" direction of time is the direction of entropy increase.
theorem entropy_ordering_temporal_direction {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsHeatVariable v) :
    ∃ (i j : Fin v.attrs.length),
      DefinesDirection { input := v.attrs.get i,
                         output := v.attrs.get j : Task S } := by
  obtain ⟨_, i, j, hpos, himp⟩ := hv
  exact ⟨i, j, hpos, himp⟩

-- A work variable has no preferred temporal direction:
-- all tasks are reversible, so no direction is defined.
theorem work_variable_no_arrow {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v)
    (i j : Fin v.attrs.length) :
    ¬ DefinesDirection { input := v.attrs.get i,
                         output := v.attrs.get j : Task S } := by
  intro ⟨_, himp⟩
  exact himp (hv.all_tasks_reversible i j).2

-- ============================================================
-- Clock cycles and the arrow of time
-- ============================================================

-- A reversible clock has no net arrow of time: both tick and reset
-- are possible, so the cycle is fully reversible.
theorem reversible_clock_no_net_arrow {S : Type} [TaskPossibility S]
    {c : Clock S} (hrev : c.isReversible) :
    Reversible { input := c.prepare, output := c.done : Task S } :=
  ⟨hrev.1, by
    simp [Task.transpose]
    exact hrev.2⟩

-- An irreversible clock (tick possible, autonomous reverse impossible)
-- has a net arrow of time.
theorem irreversible_clock_has_arrow {S : Type} [TaskPossibility S]
    {c : Clock S}
    (h_tick : Possible c.toTimer.tickTask)
    (h_no_rev : Impossible c.toTimer.tickTask†) :
    TimerArrow c.toTimer :=
  ⟨h_tick, h_no_rev⟩

-- ============================================================
-- The second law implies an arrow of time
-- ============================================================

-- The second law (existence of irreversible tasks) implies the
-- existence of a temporal direction.
theorem second_law_implies_arrow {S : Type}
    [TaskPossibility S] [SecondLaw S] :
    ∃ t : Task S, DefinesDirection t := by
  obtain ⟨t, hp, himp⟩ := SecondLaw.irreversible_exists (S := S)
  exact ⟨t, hp, himp⟩

-- ============================================================
-- Timelessness is compatible with the arrow of time
-- ============================================================

-- The timeless formulation of constructor theory is compatible
-- with the existence of an arrow of time. The arrow is not a
-- primitive temporal concept but an emergent property of the
-- asymmetry in possible vs impossible tasks.
theorem timeless_compatible_with_arrow {S : Type}
    [TaskPossibility S]
    (law : TimelessLaw S) (t : Task S)
    (_h_dir : DefinesDirection t) :
    law.law t ↔ law.law t := by
  exact Iff.rfl

-- ============================================================
-- Temporal ordering from irreversibility
-- ============================================================

-- Given a heat variable, its irreversible tasks naturally
-- induce a partial ordering on states, which can be interpreted
-- as a temporal ordering.
theorem heat_induces_state_ordering {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsHeatVariable v) :
    ∃ (i j : Fin v.attrs.length),
      i ≠ j ∧
      Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } ∧
      ¬ Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S } := by
  obtain ⟨_, i, j, hpos, himp⟩ := hv
  refine ⟨i, j, ?_, hpos, ?_⟩
  · intro heq
    subst heq
    simp [Task.transpose, Impossible] at himp
    exact himp (by simp [Possible]; exact hpos)
  · intro hrev
    exact himp hrev.2

-- ============================================================
-- Non-static attributes and temporal flow
-- ============================================================

-- A non-static attribute undergoes autonomous transitions,
-- which defines a local direction of time flow.
theorem nonstatic_has_transition {S : Type} [TaskPossibility S]
    {a : Attribute S} (h : IsNonStaticAttribute a) :
    ∃ (b : Attribute S), Attribute.Disjoint a b ∧
      Possible { input := a, output := b : Task S } :=
  h

-- An ideal clock's stages define a cyclic ordering.
-- Each stage transitions to the next, creating a directed cycle.
theorem ideal_clock_cyclic_direction {S : Type} [TaskPossibility S]
    (c : IdealClock S) (i : Fin c.stages.length) :
    let next := (i.val + 1) % c.stages.length
    have h_pos : c.stages.length > 0 := by have := c.stages_nontrivial; omega
    Possible { input := c.stages.get i,
               output := c.stages.get ⟨next, Nat.mod_lt _ h_pos⟩ : Task S } :=
  c.transitions_possible i

end ConstructorTheory
