-- Constructor Theory Formalization in Lean 4
-- Formalizing David Deutsch & Chiara Marletto's constructor theory.
-- See: https://arxiv.org/abs/1210.7439, https://arxiv.org/abs/1405.5563
-- See: https://arxiv.org/abs/1608.02625 (thermodynamics)
-- See: https://arxiv.org/abs/2505.08692 (time)
-- See: https://arxiv.org/abs/1407.0681 (life)
-- See: https://arxiv.org/abs/2401.05364 (process theory)
-- See: https://arxiv.org/abs/1507.03287 (probability)
-- See: https://arxiv.org/abs/2404.07786 (work extraction from coherence)

-- Core definitions
import ConstructorTheory.Basic
import ConstructorTheory.Composition
import ConstructorTheory.Possible

-- Principles
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Principles.Locality
import ConstructorTheory.Principles.CompositionPrinciple
import ConstructorTheory.Principles.Interoperability
import ConstructorTheory.Principles.CategoryStructure
import ConstructorTheory.Principles.ProcessTheory
import ConstructorTheory.Principles.Probability
import ConstructorTheory.Principles.Unification

-- Information theory
import ConstructorTheory.Information.Basic
import ConstructorTheory.Information.InformationMedium
import ConstructorTheory.Information.Interoperability
import ConstructorTheory.Information.Observable
import ConstructorTheory.Information.NoCloning

-- Thermodynamics
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.HeatMedia
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Thermodynamics.Entropy
import ConstructorTheory.Thermodynamics.Carnot
import ConstructorTheory.Thermodynamics.InfoThermo
import ConstructorTheory.Thermodynamics.WorkCoherence

-- Constructor theory of time
import ConstructorTheory.Time.Basic
import ConstructorTheory.Time.Duration
import ConstructorTheory.Time.ArrowOfTime

-- Constructor theory of life
import ConstructorTheory.Life.Basic
import ConstructorTheory.Life.Evolution
import ConstructorTheory.Life.InfoLife
