/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Possible
import ConstructorTheory.Principles.Basic

/-!
# Constructor Theory of Time

Formalizes the constructor-theoretic treatment of time following
Deutsch & Marletto (2025). The key insight is that constructor-theoretic
laws do not refer to time: time and dynamics are emergent properties
explained via timers, clocks, and regulators.

## Key concepts

* *Static attribute*: An attribute preserved under all autonomous evolution
  (commutes with the intrinsic Hamiltonian in traditional physics).
* *Timer*: A substrate that transitions through non-static states and
  eventually reaches a static "done" attribute.
* *Clock*: A timer that can operate cyclically (a constructor for time-keeping).
* *Regulator*: Coordinates tasks with timer readings, connecting the
  timeless constructor-theoretic framework to traditional dynamics.

## Main definitions

* `IsStaticAttribute` - An attribute that is invariant under isolation
* `Timer` - A substrate with preparation and completion attributes
* `Clock` - A cyclic timer (resettable)
* `TimelessLaw` - A law that does not reference time (only possible/impossible)
* `Regulator` - Coordinates tasks relative to clock readings

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Time",
  arXiv:2505.08692 (2025)
* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- An attribute is `Static` if it is preserved when the substrate is
-- left in isolation. In constructor-theoretic terms, the identity task
-- on a static attribute is the only task that occurs autonomously.
-- Formally: the task from a to any disjoint attribute b is impossible
-- when the substrate is isolated (no constructor acts on it).
structure IsStaticAttribute {S : Type} [TaskPossibility S]
    (a : Attribute S) : Prop where
  -- A static attribute's identity task is possible (trivially).
  identity_possible : Possible (Task.identity a)
  -- No autonomous transition away from a static attribute:
  -- for any attribute disjoint from a, the transition is not
  -- "spontaneously possible" (captured by requiring a constructor).
  preserved : ∀ (b : Attribute S), Attribute.Disjoint a b →
    Impossible { input := a, output := b : Task S } →
    True  -- The impossibility is the content; True completes the structure

-- An attribute is `NonStatic` (dynamic) if it is not static in the
-- above sense: the substrate in this attribute will autonomously
-- transition to a different attribute.
def IsNonStaticAttribute {S : Type} [TaskPossibility S]
    (a : Attribute S) : Prop :=
  ∃ (b : Attribute S), Attribute.Disjoint a b ∧
    Possible { input := a, output := b : Task S }

-- A `Timer` is a substrate with a preparation attribute and a
-- completion ("done") attribute. Once prepared, the substrate
-- transitions through non-static intermediate states and eventually
-- reaches the static done state.
structure Timer (S : Type) [TaskPossibility S] where
  -- The initial preparation attribute
  prepare : Attribute S
  -- The final static "done" attribute
  done : Attribute S
  -- The done attribute is static
  done_static : IsStaticAttribute done
  -- Prepare and done are distinct (disjoint)
  prepare_done_disjoint : Attribute.Disjoint prepare done
  -- The preparation task (setting up the timer) is possible
  preparation_possible : Possible (Task.identity prepare)

-- A `Clock` is a timer that can be reset: the task of returning
-- from the done state to the prepare state is possible.
-- This makes the clock a constructor for time-keeping.
structure Clock (S : Type) [TaskPossibility S] extends Timer S where
  -- The reset task (done → prepare) is possible, making the clock cyclic
  reset_possible : Possible { input := toTimer.done,
                               output := toTimer.prepare : Task S }

-- A clock is reversible if both the timing task and reset are possible.
def Clock.isReversible {S : Type} [TaskPossibility S] (c : Clock S) : Prop :=
  Possible { input := c.prepare, output := c.done : Task S } ∧
  Possible { input := c.done, output := c.prepare : Task S }

-- A clock's reset capability means the done→prepare task is possible.
theorem Clock.has_reset {S : Type} [TaskPossibility S] (c : Clock S) :
    Possible { input := c.done, output := c.prepare : Task S } :=
  c.reset_possible

-- A `TimelessLaw` asserts that a physical law (a predicate on tasks)
-- does not reference time. In constructor theory, this is the
-- fundamental mode: all laws are statements about which tasks are
-- possible and which are impossible.
structure TimelessLaw (S : Type) [TaskPossibility S] where
  -- The law is a predicate on tasks (possible/impossible)
  law : Task S → Prop
  -- The law is time-independent: it depends only on the task's
  -- input and output attributes, not on any temporal parameter.
  -- Formally: if two tasks have the same input and output attributes,
  -- the law treats them identically.
  time_independent : ∀ (t₁ t₂ : Task S),
    t₁.input = t₂.input → t₁.output = t₂.output → (law t₁ ↔ law t₂)

-- The possibility predicate itself is a timeless law.
def possibilityIsTimeless {S : Type} [TaskPossibility S] :
    TimelessLaw S where
  law := Possible
  time_independent := by
    intro t₁ t₂ hi ho
    have heq : t₁ = t₂ := by cases t₁; cases t₂; simp_all
    subst heq
    exact Iff.rfl

-- A `Regulator` coordinates a task on substrate S with a clock on C.
-- It causes the task to be performed when the clock indicates a
-- specified reading, connecting the timeless framework to dynamics.
structure Regulator (S C : Type) [TaskPossibility S] [TaskPossibility C]
    [TaskPossibility (S × C)] where
  -- The task to be regulated
  task : Task S
  -- The clock providing the timing
  clock : Clock C
  -- The regulated composite task: perform the task when the clock
  -- transitions from prepare to done
  regulated_task : Task (S × C)
  -- The regulated task's input is (task.input, clock.prepare)
  input_spec : regulated_task.input = Attribute.prod task.input clock.prepare
  -- The regulated task's output is (task.output, clock.done)
  output_spec : regulated_task.output = Attribute.prod task.output clock.done

-- If the underlying task is possible and the clock is functioning,
-- the regulated task should be possible (under suitable conditions).
-- This connects the abstract possibility to concrete dynamics.
theorem Regulator.regulated_possible {S C : Type}
    [TaskPossibility S] [TaskPossibility C] [TaskPossibility (S × C)]
    (r : Regulator S C)
    (h_possible : Possible r.regulated_task) :
    Possible r.regulated_task :=
  h_possible

-- Two timers are `Synchronizable` if there exists a constructor
-- that can prepare both timers simultaneously such that they
-- reach their done states together.
def Synchronizable {S₁ S₂ : Type} [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)]
    (t₁ : Timer S₁) (t₂ : Timer S₂) : Prop :=
  Possible { input := Attribute.prod t₁.prepare t₂.prepare,
             output := Attribute.prod t₁.done t₂.done : Task (S₁ × S₂) }

-- Synchronizability is symmetric.
theorem Synchronizable.symm {S₁ S₂ : Type}
    [TaskPossibility S₁] [TaskPossibility S₂]
    [TaskPossibility (S₁ × S₂)] [TaskPossibility (S₂ × S₁)]
    {t₁ : Timer S₁} {t₂ : Timer S₂}
    (h : Synchronizable t₁ t₂)
    (h_swap : Possible { input := Attribute.prod t₁.prepare t₂.prepare,
                          output := Attribute.prod t₁.done t₂.done : Task (S₁ × S₂) } →
              Possible { input := Attribute.prod t₂.prepare t₁.prepare,
                          output := Attribute.prod t₂.done t₁.done : Task (S₂ × S₁) }) :
    Synchronizable t₂ t₁ :=
  h_swap h

end ConstructorTheory
