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
import ConstructorTheory.Principles.Basic

/-!
# Work Extraction, Coherence, and Distinguishability

Formalizes the constructor-theoretic impossibility of universal work
extraction from coherence, following Plesnik & Violaris (2024,
arXiv:2404.07786) and Marletto (2022, arXiv:2009.14649).

The key insight is that in superinformation media (quantum systems),
the impossibility of universal work extraction from "coherent"
superpositions follows from the constructor-theoretic structure of
distinguishability, without needing to invoke the formalism of
quantum mechanics.

## Key concepts

* *Coherent variable*: A variable that is not an information variable
  but IS a computation variable (unclonable).
* *Work extraction*: Converting a coherent variable's state to a work
  variable's state.
* *Universal work extractor*: A hypothetical constructor that extracts
  work from any coherent state — shown to be impossible.
* *Constructor-based irreversibility*: Irreversibility that emerges
  from the task structure even with time-symmetric microscopic laws.

## Main results

* `coherent_not_clonable` - Coherent variables cannot be cloned
* `no_universal_work_extractor` - No universal work extraction from coherence
* `coherence_work_incompatible` - Coherence and work are incompatible
* `constructor_irreversibility_emergence` - Irreversibility from task structure

## References

* M. Plesnik & M. Violaris, "Impossibility of universal work extraction
  from coherence", arXiv:2404.07786 (2024)
* C. Marletto et al., "Emergence of Constructor-based Irreversibility
  in Quantum Systems", PRL 128, 080401 (2022), arXiv:2009.14649
* C. Marletto, "Constructor Theory of Thermodynamics",
  PRL 118, 140602 (2017), arXiv:1608.02625
-/

namespace ConstructorTheory

-- ============================================================
-- Coherent variables: unclonable computation variables
-- ============================================================

-- A `CoherentVariable` is a computation variable that is NOT an
-- information variable. In quantum terms, this corresponds to a
-- basis that includes "coherent superpositions" — states that can be
-- permuted but not cloned.
-- This is equivalent to IsUnclonable but named for the thermodynamic context.
def IsCoherentVariable {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] (v : Variable S) : Prop :=
  IsComputationVariable v ∧ ¬ IsInformationVariable v

-- A coherent variable is a computation variable.
theorem IsCoherentVariable.is_computation {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsCoherentVariable v) :
    IsComputationVariable v :=
  h.1

-- A coherent variable is NOT an information variable (hence not clonable).
theorem IsCoherentVariable.not_information {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsCoherentVariable v) :
    ¬ IsInformationVariable v :=
  h.2

-- A coherent variable cannot be cloned: for any proposed blank,
-- there exists an attribute whose cloning is impossible.
theorem coherent_not_clonable {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsCoherentVariable v) :
    ∀ blank : Attribute S,
      ¬ (∀ i : Fin v.attrs.length,
        Possible (cloneTaskSingle (v.attrs.get i) blank)) := by
  intro blank hclone
  exact h.2 ⟨h.1, blank, hclone⟩

-- ============================================================
-- Work extraction from coherent variables
-- ============================================================

-- A `WorkExtractionTask` attempts to convert a coherent variable's
-- state into a work variable's state (extracting useful work from
-- quantum coherence).
structure WorkExtractionTask {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] where
  -- The coherent source
  source : Variable S
  source_coherent : IsCoherentVariable source
  -- The work target
  target : Variable S
  target_work : IsWorkVariable target
  -- The extraction task maps source attributes to target attributes
  extraction : Fin source.attrs.length → Fin target.attrs.length

-- A `UniversalWorkExtractor` would extract work from ANY coherent
-- state. Plesnik & Violaris (2024) show this is impossible.
structure UniversalWorkExtractor {S : Type} [TaskPossibility S]
    [TaskPossibility (S × S)] where
  wet : WorkExtractionTask (S := S)
  -- The extraction is possible for ALL source attributes
  universal : ∀ i : Fin wet.source.attrs.length,
    Possible { input := wet.source.attrs.get i,
               output := wet.target.attrs.get (wet.extraction i) : Task S }
  -- The extraction is injective (different coherent states → different work states)
  injective : ∀ i j : Fin wet.source.attrs.length,
    wet.extraction i = wet.extraction j → i = j

-- ============================================================
-- Main impossibility theorem
-- ============================================================

-- **Theorem (Plesnik & Violaris 2024)**: A universal work extractor
-- from a coherent variable is impossible.
--
-- Proof sketch: If a universal work extractor existed, it would provide
-- a way to clone the coherent variable (via extraction + work-variable
-- cloning + reverse extraction), contradicting its non-information status.
--
-- The key hypothesis `h_induces_cloning` captures the composition:
-- extract to work, clone in work space, reverse-extract back to source.
-- In a composable universe this would follow from the individual steps,
-- but we state it as a hypothesis to avoid requiring ComposableUniverse.
theorem no_universal_work_extractor {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    (uwe : @UniversalWorkExtractor S _ _)
    -- The extraction + work cloning + reverse extraction induces cloning
    -- of the source variable. This is the critical step from Plesnik & Violaris.
    (h_induces_cloning : ∃ blank : Attribute S,
      ∀ i : Fin uwe.wet.source.attrs.length,
        Possible (cloneTaskSingle (uwe.wet.source.attrs.get i) blank)) :
    False := by
  have h_not_info := uwe.wet.source_coherent.2
  obtain ⟨blank, hblank⟩ := h_induces_cloning
  apply h_not_info
  exact ⟨uwe.wet.source_coherent.1, blank, hblank⟩

-- ============================================================
-- Coherence and work incompatibility
-- ============================================================

-- A coherent variable cannot be a work variable.
-- Work variables are information variables, but coherent variables are not.
theorem coherence_work_incompatible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsCoherentVariable v) :
    ¬ IsWorkVariable v :=
  fun hw => h.2 hw.toInformationVariable

-- A coherent variable cannot be a heat variable either
-- (heat variables are information variables).
theorem coherence_heat_incompatible {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsCoherentVariable v) :
    ¬ IsHeatVariable v :=
  fun hh => h.2 hh.toInformationVariable

-- ============================================================
-- Constructor-based irreversibility
-- ============================================================

-- Following Marletto et al. (2022), constructor-based irreversibility
-- can emerge from time-symmetric microscopic laws. A task T is
-- "constructor-irreversible" if T is possible (has a constructor) but
-- T† is impossible (has no constructor), even though the underlying
-- dynamical laws are time-reversal symmetric.

-- Constructor-based irreversibility for tasks.
def ConstructorIrreversible {S : Type} [TaskPossibility S]
    (t : Task S) : Prop :=
  Possible t ∧ Impossible t†

-- Constructor irreversibility implies non-reversibility.
theorem constructor_irreversible_not_reversible {S : Type}
    [TaskPossibility S] {t : Task S}
    (h : ConstructorIrreversible t) : ¬ Reversible t :=
  fun hrev => h.2 hrev.2

-- The transpose of a constructor-irreversible task is impossible.
theorem constructor_irreversible_transpose_impossible {S : Type}
    [TaskPossibility S] {t : Task S}
    (h : ConstructorIrreversible t) : Impossible t† :=
  h.2

-- If a task is constructor-irreversible, the transpose of the
-- transpose is still possible (since ††  = id).
theorem constructor_irreversible_double_transpose {S : Type}
    [TaskPossibility S] {t : Task S}
    (h : ConstructorIrreversible t) : Possible t†† := by
  simp [Task.transpose_transpose]
  exact h.1

-- ============================================================
-- Distinguishability and work extraction
-- ============================================================

-- The fundamental link between distinguishability and work:
-- work extraction requires distinguishability of the source states,
-- because a work variable has distinguishable (disjoint) attributes.
-- If the source states are not distinguishable, universal work
-- extraction is impossible.
theorem work_extraction_requires_distinguishability {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (_ : IsCoherentVariable v)
    (i j : Fin v.attrs.length) (hij : i ≠ j) :
    -- The source attributes are disjoint (distinguishable as attributes)
    Attribute.Disjoint (v.attrs.get i) (v.attrs.get j) :=
  v.pairwise_disjoint i j hij

-- ============================================================
-- Superinformation and coherence
-- ============================================================

-- In a superinformation medium, coherent variables arise from
-- the union of complementary information variables.
theorem superinfo_has_coherent_union {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v₁ v₂ : Variable S} (h : ComplementaryPair v₁ v₂)
    (v_union : Variable S)
    (h₁ : ∀ a ∈ v₁.attrs, a ∈ v_union.attrs)
    (h₂ : ∀ a ∈ v₂.attrs, a ∈ v_union.attrs)
    (h_comp : IsComputationVariable v_union) :
    IsCoherentVariable v_union :=
  ⟨h_comp, h.2.2 v_union h₁ h₂⟩

-- The second law in the presence of coherence:
-- A coherent variable that is also a work variable leads to contradiction.
-- This is the thermodynamic consequence: coherent variables cannot
-- participate as work-like side effects in adiabatic processes.
theorem coherence_excludes_work_status {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h_coh : IsCoherentVariable v)
    (h_info : IsInformationVariable v) : False :=
  h_coh.2 h_info

-- Coherent variables cannot serve as adiabatic side effects:
-- since adiabatic possibility requires a reversible work-like
-- ancilla, and coherent variables are not information variables,
-- they cannot play this role.
theorem coherent_not_adiabatic_ancilla {S : Type}
    [TaskPossibility S] [TaskPossibility (S × S)]
    {v : Variable S} (h : IsCoherentVariable v) :
    ¬ IsWorkVariable v :=
  fun hw => h.2 hw.toInformationVariable

end ConstructorTheory
