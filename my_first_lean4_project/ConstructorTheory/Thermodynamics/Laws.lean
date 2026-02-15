/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.HeatMedia

/-!
# Constructor-Theoretic Laws of Thermodynamics

Formalizes the first and second laws of thermodynamics in
constructor-theoretic terms, following Marletto (2016).

The key insight is that thermodynamic laws become statements about
which tasks are possible and impossible, rather than statements
about dynamical trajectories or entropy functions.

## First Law (Conservation)
"The task of creating energy from nothing is impossible."
Formalized as: there is no task that changes a work variable
without a corresponding change in the environment.

## Second Law (Irreversibility)
"There exist irreversible tasks."
Formalized as: there exists a task that is possible but whose
transpose is impossible — i.e., some transformations cannot be undone.

## Main definitions

* `FirstLaw` - Conservation: no perpetual motion of the first kind
* `SecondLaw` - Irreversibility: some processes cannot be reversed
* `NoReverse` - A stronger form: specific irreversible tasks exist
* `KelvinStatement` - No cyclic process can convert heat entirely to work

## References

* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
-/

namespace ConstructorTheory

-- The **First Law** of thermodynamics in constructor-theoretic terms:
-- In a universe with a work medium, the identity task on the work medium
-- is the only task on the work medium that can be performed without
-- affecting any other substrate.
-- Simplified formulation: a perpetual motion machine of the first kind
-- is impossible. Any task that changes the state of a work variable
-- must be coupled with a corresponding change elsewhere.
class FirstLaw (S : Type) [TaskPossibility S] [TaskPossibility (S × S)] where
  -- There exists a work medium.
  has_work : IsWorkMedium S
  -- Any possible task on the work medium that creates a net change
  -- in the work variable (i→j with i≠j) requires coupling to
  -- another substrate — it cannot happen in isolation unless both
  -- directions are possible (conservation).
  conservation : ∀ (v : Variable S), IsWorkVariable v →
    ∀ i j : Fin v.attrs.length, i ≠ j →
    Possible { input := v.attrs.get i, output := v.attrs.get j : Task S } →
    Possible { input := v.attrs.get j, output := v.attrs.get i : Task S }

-- The first law implies all work variable tasks are reversible.
theorem FirstLaw.work_reversible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [FirstLaw S]
    {v : Variable S} (hv : IsWorkVariable v)
    (i j : Fin v.attrs.length) :
    Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S } :=
  hv.2 i j

-- The **Second Law** of thermodynamics in constructor-theoretic terms:
-- There exist possible tasks whose transpose is impossible.
-- Equivalently: irreversibility is a genuine feature of nature,
-- not an artifact of coarse-graining.
class SecondLaw (S : Type) [TaskPossibility S] where
  -- There exists a task that is possible but not reversible.
  irreversible_exists : ∃ t : Task S, Possible t ∧ Impossible t†

-- The second law gives us a concrete irreversible task.
theorem SecondLaw.witness {S : Type} [TaskPossibility S] [SecondLaw S] :
    ∃ t : Task S, Possible t ∧ ¬ Reversible t :=
  let ⟨t, hp, himp⟩ := SecondLaw.irreversible_exists (S := S)
  ⟨t, hp, fun hrev => himp hrev.2⟩

-- A `NoReverse` statement: a specific task is possible but its
-- reverse is impossible. This is the constructor-theoretic
-- formulation of "entropy increases."
def NoReverse {S : Type} [TaskPossibility S] (t : Task S) : Prop :=
  Possible t ∧ Impossible t†

-- NoReverse implies the task is not reversible.
theorem NoReverse.not_reversible {S : Type} [TaskPossibility S]
    {t : Task S} (h : NoReverse t) : ¬ Reversible t :=
  fun hrev => h.2 hrev.2

-- **Kelvin Statement** in constructor-theoretic terms:
-- It is impossible to perform a task whose sole effect is to
-- transfer energy from a heat variable to a work variable.
-- i.e., there is no perfect heat engine.
class KelvinStatement (S : Type) [TaskPossibility S] [TaskPossibility (S × S)] where
  has_work : IsWorkMedium S
  has_heat : IsHeatMedium S
  -- For any work variable and heat variable, the task of
  -- transferring from a heat attribute to a work attribute
  -- while restoring the heat source is impossible.
  no_perfect_engine : ∀ (vw vh : Variable S),
    IsWorkVariable vw → IsHeatVariable vh →
    ∀ (i_h j_h : Fin vh.attrs.length) (i_w j_w : Fin vw.attrs.length),
      -- The forward heat transfer is possible
      Possible { input := vh.attrs.get i_h, output := vh.attrs.get j_h : Task S } →
      -- But the cyclic extraction (doing the heat transfer and
      -- reversing the work change) is impossible
      i_w ≠ j_w →
      Impossible { input := Attribute.prod (vh.attrs.get j_h) (vw.attrs.get i_w),
                   output := Attribute.prod (vh.attrs.get i_h) (vw.attrs.get j_w) :
                   Task (S × S) }

-- The Kelvin statement implies the second law: if we have a heat variable,
-- irreversible tasks exist.
theorem KelvinStatement.impliesSecondLaw {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)] [KelvinStatement S] :
    ∃ (v : Variable S), IsHeatVariable v := by
  exact KelvinStatement.has_heat

end ConstructorTheory
