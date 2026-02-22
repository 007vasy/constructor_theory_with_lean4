-- Constructor Theory Formalization in Lean 4
-- Formalizing David Deutsch & Chiara Marletto's constructor theory.
-- See: https://arxiv.org/abs/1210.7439, https://arxiv.org/abs/1405.5563
-- See: https://arxiv.org/abs/1608.02625 (thermodynamics)
-- See: https://arxiv.org/abs/2505.08692 (time)
-- See: https://arxiv.org/abs/1407.0681 (life)

-- Core definitions
import ConstructorTheory.Basic
import ConstructorTheory.Composition
import ConstructorTheory.Possible

-- Principles
import ConstructorTheory.Principles.Basic
import ConstructorTheory.Principles.Locality
import ConstructorTheory.Principles.CompositionPrinciple

-- Information theory
import ConstructorTheory.Information.Basic
import ConstructorTheory.Information.InformationMedium
import ConstructorTheory.Information.Interoperability
import ConstructorTheory.Information.Observable

-- Thermodynamics
import ConstructorTheory.Thermodynamics.Basic
import ConstructorTheory.Thermodynamics.HeatMedia
import ConstructorTheory.Thermodynamics.Laws
import ConstructorTheory.Thermodynamics.Entropy

-- Constructor theory of time
import ConstructorTheory.Time.Basic

-- Constructor theory of life
import ConstructorTheory.Life.Basic
