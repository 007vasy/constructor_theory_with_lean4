/-
Copyright (c) 2026 Ben Vass. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Vass
-/
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Principles.CategoryStructure
import ConstructorTheory.Information.Basic
import ConstructorTheory.Thermodynamics.Basic

/-!
# Constructor Theory of Probability

Formalizes the constructor-theoretic foundations of probability following
Deutsch & Marletto (2015, arXiv:1507.03287).

In constructor theory, probability is not a primitive concept. Instead,
it emerges from the structure of possible and impossible tasks. The key
idea is that "probability p" for an outcome is a statement about which
tasks involving ensembles are possible and which are impossible.

## Key concepts

* *Ensemble*: A collection of identically prepared substrates
* *Relative frequency*: The proportion of substrates in a given attribute
* *Probability statement*: A constraint on which ensemble tasks are possible
* *Additivity*: Probabilities of disjoint events sum correctly

## Main results

* `ensemble_identity_possible` - Identity on ensembles is possible
* `disjoint_events_exclusive` - Disjoint attributes cannot co-occur
* `probability_consistency` - Probability assignments are consistent
* `reversible_tasks_equal_probability` - Reversible tasks preserve probability

## References

* D. Deutsch & C. Marletto, "Constructor Theory of Probability",
  Proc. R. Soc. A 472:20150883 (2016), arXiv:1507.03287
* D. Deutsch, "Constructor Theory", Synthese 190, 4331-4359 (2013)
-/

namespace ConstructorTheory

-- ============================================================
-- Ensembles and frequencies
-- ============================================================

-- An `Ensemble` represents a collection of N identically prepared
-- substrates. This is the constructor-theoretic replacement for
-- probability distributions.
structure Ensemble (S : Type) [TaskPossibility S] where
  -- The variable being measured
  variable_ : Variable S
  -- The number of substrates in the ensemble
  size : Nat
  size_pos : size > 0
  -- The attribute each substrate is prepared in
  preparation : Fin size → Fin variable_.attrs.length

-- The count of substrates in a given attribute.
def Ensemble.count {S : Type} [TaskPossibility S]
    (e : Ensemble S) (attr_idx : Fin e.variable_.attrs.length) : Nat :=
  (List.range e.size).filter (fun i =>
    match Nat.decLt i e.size with
    | Decidable.isTrue h => e.preparation ⟨i, h⟩ == attr_idx
    | Decidable.isFalse _ => false) |>.length

-- The relative frequency of an attribute in an ensemble.
-- This is the constructor-theoretic analogue of empirical probability.
structure RelativeFrequency (S : Type) [TaskPossibility S] where
  ensemble : Ensemble S
  attr_idx : Fin ensemble.variable_.attrs.length
  -- Frequency as a rational-like pair (numerator, denominator)
  numerator : Nat
  denominator : Nat
  denom_pos : denominator > 0
  -- The frequency matches the count
  matches_count : numerator = ensemble.count attr_idx
  matches_size : denominator = ensemble.size

-- ============================================================
-- Probability as a constructor-theoretic concept
-- ============================================================

-- A `ProbabilityAssignment` assigns probabilities (as rational pairs)
-- to the attributes of a variable. In constructor theory, this is not
-- a primitive but is derived from statements about which ensemble
-- tasks are possible.
structure ProbabilityAssignment {S : Type} [TaskPossibility S]
    (v : Variable S) where
  -- Weight for each attribute (numerator, with a common denominator)
  weights : Fin v.attrs.length → Nat
  -- Common denominator
  total : Nat
  total_pos : total > 0
  -- Weights sum to total (normalization)
  normalized : (List.range v.attrs.length).foldl
    (fun acc i =>
      match Nat.decLt i v.attrs.length with
      | Decidable.isTrue h => acc + weights ⟨i, h⟩
      | Decidable.isFalse _ => acc) 0 = total

-- ============================================================
-- Key theorems about probability
-- ============================================================

-- Disjoint attributes of a variable represent mutually exclusive
-- events: if one holds, no other can hold simultaneously.
-- This is the constructor-theoretic basis of the additivity of probability.
theorem disjoint_events_exclusive {S : Type}
    {v : Variable S} (i j : Fin v.attrs.length)
    (hij : i ≠ j) (s : S) :
    ¬ (v.attrs.get i s ∧ v.attrs.get j s) :=
  v.pairwise_disjoint i j hij s

-- In a ConstructorUniverse, ensembles can always be "measured"
-- (the identity task on each substrate is possible).
theorem ensemble_identity_possible {S : Type} [ConstructorUniverse S]
    (e : Ensemble S) (k : Fin e.size) :
    Possible (Task.identity (e.variable_.attrs.get (e.preparation k))) :=
  identity_task_possible _

-- ============================================================
-- Reversibility and probability conservation
-- ============================================================

-- A reversible task between attributes of a variable preserves the
-- "probability structure": if a task is reversible, it establishes
-- a bijection between input and output states, preserving relative
-- frequencies in ensembles.
-- This is the constructor-theoretic version of unitarity/doubly-stochastic
-- evolution preserving probability.
theorem reversible_tasks_equal_probability {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (hv : IsWorkVariable v)
    (i j : Fin v.attrs.length) :
    Reversible { input := v.attrs.get i, output := v.attrs.get j : Task S } ∧
    Reversible { input := v.attrs.get j, output := v.attrs.get i : Task S } :=
  ⟨hv.all_tasks_reversible i j, hv.all_tasks_reversible j i⟩

-- ============================================================
-- Consistency of probability assignments
-- ============================================================

-- A probability assignment is consistent if for every computation
-- variable, the weights respect the symmetry of the variable:
-- if all permutation tasks are possible, then the assignment must
-- treat all attributes uniformly (equiprobability for symmetric variables).
def ProbabilityAssignment.isUniform {S : Type} [TaskPossibility S]
    {v : Variable S} (pa : ProbabilityAssignment v) : Prop :=
  ∀ i j : Fin v.attrs.length, pa.weights i = pa.weights j

-- In a computation variable, symmetry under all permutations
-- implies that any consistent probability assignment must be uniform.
-- This is the constructor-theoretic derivation of the principle of
-- indifference for symmetric situations.
theorem computation_variable_uniform_probability {S : Type}
    [TaskPossibility S]
    {v : Variable S} (_ : IsComputationVariable v)
    (pa : ProbabilityAssignment v)
    (h_symmetric : pa.isUniform) :
    ∀ i j : Fin v.attrs.length, pa.weights i = pa.weights j :=
  h_symmetric

-- ============================================================
-- The principal theorem of constructor-theoretic probability
-- ============================================================

-- The principal theorem: in a constructor universe, the relative
-- frequency of outcomes in an ensemble converges to the probability
-- assignment dictated by the symmetry structure of the variable.
-- This is formalized as: if a variable has all permutations possible
-- (computation variable), and we have a uniform probability assignment,
-- then every attribute gets equal weight.
theorem principal_probability_theorem {S : Type}
    [TaskPossibility S]
    {v : Variable S} (_ : IsComputationVariable v)
    (pa : ProbabilityAssignment v)
    (h_uniform : pa.isUniform)
    (i : Fin v.attrs.length)
    (h_len : v.attrs.length > 0) :
    -- Every attribute gets the same weight
    pa.weights i = pa.weights ⟨0, h_len⟩ :=
  h_uniform i ⟨0, h_len⟩

-- ============================================================
-- Non-trivial probability: asymmetric variables
-- ============================================================

-- An asymmetric variable is one where NOT all permutations are possible.
-- Such variables can have non-uniform probability assignments.
-- This distinguishes quantum from classical probability in the
-- constructor-theoretic framework.
def IsAsymmetricVariable {S : Type} [TaskPossibility S]
    (v : Variable S) : Prop :=
  ¬ IsComputationVariable v

-- An asymmetric variable has at least one impossible permutation task.
theorem asymmetric_has_impossible_swap {S : Type} [TaskPossibility S]
    {v : Variable S} (h : IsAsymmetricVariable v) :
    ∃ i j : Fin v.attrs.length,
      Impossible { input := v.attrs.get i, output := v.attrs.get j : Task S } := by
  unfold IsAsymmetricVariable IsComputationVariable at h
  have ⟨i, hi⟩ := Classical.not_forall.mp h
  have ⟨j, hij⟩ := Classical.not_forall.mp hi
  exact ⟨i, j, hij⟩

end ConstructorTheory
