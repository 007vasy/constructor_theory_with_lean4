/-
  Lean 4 Draft based on "Constructor Theory of Time" by Deutsch & Marletto (May 2025 draft)
  This is a high-level structural translation. Many concepts are opaque or axiomatic.
-/

universe u

/-!
## Section 3: Possible and impossible tasks
Core concepts: Substrate, State, Attribute, Task, Possibility.
-/

-- A physical system or substrate.
opaque Substrate : Type u

-- A state of a substrate.
opaque State (Σ : Substrate) : Type u

-- An attribute of a physical system is a set of some of the system’s possible states.
@[reducible]
def Attribute (Σ : Substrate) : Type u := Set (State Σ)

-- Composition of two distinct substrates.
opaque substrate_compose (Σ₁ Σ₂ : Substrate) : Substrate
infixr:65 " ⊕Σ " => substrate_compose -- Using ⊕Σ to distinguish from other uses of ⊕

-- The paper asserts (Sec 3, Locality): "There exists a description where attributes of substrates are such that
-- any attribute of a composite substrate A ⊕ B is an ordered pair of attributes (a,b) of substrate A and substrate B".
-- This implies `Attribute (Σ₁ ⊕Σ Σ₂)` is structurally equivalent to `Attribute Σ₁ × Attribute Σ₂`.
-- We assume this structural equivalence for composite attributes.
-- A more rigorous approach might involve type isomorphisms.
@[reducible]
def ProductAttribute (Σ₁ Σ₂ : Substrate) : Type u := Attribute Σ₁ × Attribute Σ₂

axiom composite_attribute_is_product_like {Σ₁ Σ₂ : Substrate} :
  Nonempty (Equiv (Attribute (Σ₁ ⊕Σ Σ₂)) (ProductAttribute Σ₁ Σ₂))

-- For simplicity in task definitions, we'll often assume we can directly use ProductAttribute.
-- A helper to bridge this:
def to_product_attr {Σ₁ Σ₂ : Substrate} (attr_comp : Attribute (Σ₁ ⊕Σ Σ₂)) : ProductAttribute Σ₁ Σ₂ :=
  Classical.choice (composite_attribute_is_product_like Nonempty.intro)).toFun attr_comp

def from_product_attr {Σ₁ Σ₂ : Substrate} (prod_attr : ProductAttribute Σ₁ Σ₂) : Attribute (Σ₁ ⊕Σ Σ₂) :=
  Classical.choice (composite_attribute_is_product_like Nonempty.intro)).invFun prod_attr

-- A task is an ordered pair of attributes of a physical system Σ.
structure Task (Σ : Substrate) where
  inputAttribute  : Attribute Σ
  outputAttribute : Attribute Σ
  -- The paper notes: "performance of a task must produce not only a specified output
  -- but also some measurable indication that the transformation is complete".
  -- This is a complex condition, potentially tied to the constructor or output attributes.
  -- It's not explicitly part of this basic Task structure here but assumed for 'Possible' tasks.

-- Transformations that can be brought about are 'possible'.
opaque Possible {Σ : Substrate} (t : Task Σ) : Prop

-- Those that cannot are 'impossible'.
@[reducible]
def Impossible {Σ : Substrate} (t : Task Σ) : Prop := ¬ Possible t

-- Constructors are idealised devices.
opaque Constructor : Type u

-- A constructor performs a task.
opaque PerformsTask (c : Constructor) {Σ : Substrate} (t : Task Σ) : Prop

-- The paper links task possibility to constructor existence:
-- "If there is no finite bound on the accuracy or reliability ... then T is possible,
-- and a constructor for T is too".
axiom possibility_implies_constructor_exists {Σ : Substrate} (t : Task Σ) :
  Possible t → ∃ (c : Constructor), PerformsTask c t
  -- The paper adds: "a possible substrate being one whose existence is not forbidden by the laws of physics."
  -- This implies the constructor `c` itself must be physically realizable.

-- Composition of tasks (serial).
-- (A → B) • (B → C) = (A → C)
def compose_tasks {Σ : Substrate} (t₁ t₂ : Task Σ) (h_compat : t₁.outputAttribute = t₂.inputAttribute) : Task Σ :=
  { inputAttribute  := t₁.inputAttribute,
    outputAttribute := t₂.outputAttribute }

-- The Composition Principle: "it requires the composition of possible tasks to be possible tasks".
axiom composition_principle {Σ : Substrate} {t₁ t₂ : Task Σ} (h_compat : t₁.outputAttribute = t₂.inputAttribute) :
  Possible t₁ → Possible t₂ → Possible (compose_tasks t₁ t₂ h_compat)

-- Locality Principle (Einstein, 1949, adapted):
-- "There exists a description where attributes of substrates are such that any attribute
-- of a composite substrate A ⊕ B is an ordered pair of attributes (a,b) ...
-- with the property that performing any task on A only, cannot change the attribute b of B."
-- This is largely captured by assuming `Attribute (A ⊕Σ B)` is like `(Attribute A) × (Attribute B)`,
-- and tasks "on A only" are structured accordingly.
-- A task `t_on_A_only : Task (A ⊕Σ B)` constructed from `task_A : Task A` would have:
-- `t_on_A_only.inputAttribute`  corresponds to `(task_A.inputAttribute, fixed_b)`
-- `t_on_A_only.outputAttribute` corresponds to `(task_A.outputAttribute, fixed_b)`
-- The principle asserts such a description (and compliant tasks) exist.

/-!
## Section 4: Isolated substrates and static attributes
-/

-- An isolated substrate: "possibility of any task on it alone depends only on its own attributes."
opaque IsIsolated (Σ : Substrate) : Prop

-- "the composite substrate of a number of isolated substrates is also isolated."
axiom isolated_composition_preserves_isolation {Σ₁ Σ₂ : Substrate} :
  IsIsolated Σ₁ → IsIsolated Σ₂ → IsIsolated (Σ₁ ⊕Σ Σ₂)

-- Static attribute: "one that it is impossible to change if the substrate is isolated."
def IsStaticAttribute {Σ : Substrate} (attr : Attribute Σ) (h_iso : IsIsolated Σ) : Prop :=
  ∀ (attr' : Attribute Σ), attr ≠ attr' →
    Impossible { inputAttribute := attr, outputAttribute := attr' : Task Σ}

/-!
## Section 5 & 6: The null task, Null Constructors, and Timers
-/

-- Null Constructor: An isolated substrate with specific attributes and internal dynamics.
-- S: Starting, R: Running, C: Completed.
structure NullConstructorDef (nc_substrate : Substrate) where
  is_isolated_nc : IsIsolated nc_substrate
  starting_attr  : Attribute nc_substrate
  running_attr   : Attribute nc_substrate
  completed_attr : Attribute nc_substrate
  -- `completed_attr` must be static for the null constructor.
  is_static_completed : IsStaticAttribute completed_attr is_isolated_nc
  -- Internal transitions:
  task_S_to_R : Task nc_substrate := { inputAttribute := starting_attr, outputAttribute := running_attr }
  task_R_to_C : Task nc_substrate := { inputAttribute := running_attr,  outputAttribute := completed_attr }
  possible_S_to_R : Possible task_S_to_R
  possible_R_to_C : Possible task_R_to_C
  -- Indication of completion: `completed_attr` must be "distinguishable" (a deeper concept).

-- The Null Task:
-- The paper argues the null task "{ }" must be possible, implying null constructors exist.
-- "A constructor for the null task shall be called a `null constructor`."
-- "a null constructor C for it doesn’t act on one and must therefore be an isolated substrate itself."
-- We represent this as the existence of substrates that satisfy `NullConstructorDef`.
axiom exists_substrate_satisfying_null_constructor_def :
  ∃ (s : Substrate), Nonempty (NullConstructorDef s)

-- Duration (e.g., non-negative real numbers).
opaque Duration : Type
instance : Zero Duration      := ⟨Classical.choice (inferInstanceAs (Inhabited Duration))⟩ -- Placeholder
instance : LT Duration       := ⟨fun _ _ => false⟩ -- Placeholder
instance : LE Duration       := ⟨fun _ _ => false⟩ -- Placeholder
instance : DecidableRel (@LT.lt Duration _) := fun _ _ => isFalse (by assumption) -- Placeholder
instance : DecidableRel (@LE.le Duration _) := fun _ _ => isFalse (by assumption) -- Placeholder
instance : DecidableEq Duration := Classical.decEq Duration -- Placeholder

-- Timer: A null constructor with an associated duration τ.
-- The attributes (α, β, γ) implicitly define/encode the duration τ.
structure TimerDef (timer_s : Substrate) (τ : Duration) extends NullConstructorDef timer_s where
  -- α (starting), β (running), γ (completed) are from `NullConstructorDef`.
  -- Halt flag: "The halt flag cannot always be chosen to coincide with the attribute γ...".
  -- For this sketch, we assume `completed_attr` (γ) serves as the halt signal or is directly related.
  -- A full model would add explicit halt flag attributes and their distinguishability.
  duration_is_positive : τ > (0 : Duration) -- Timers typically have positive duration.

-- Predicate: `s` is a timer of duration `τ`.
def IsTimer (s : Substrate) (τ : Duration) : Prop := Nonempty (TimerDef s τ)

-- Helper to get timer attributes (α for starting, γ for completed/halted state).
def timer_attr_α {s τ} (td : TimerDef s τ) : Attribute s := td.toNullConstructorDef.starting_attr
def timer_attr_γ {s τ} (td : TimerDef s τ) : Attribute s := td.toNullConstructorDef.completed_attr

-- Properties (8) and (9) for timers define an equivalence class for duration.
-- Task: "both timers, starting together, also halt together".
-- Input: (α₁, α₂), Output: (γ₁, γ₂) on timer₁ ⊕Σ timer₂.
def task_both_halt_simultaneously {s₁ s₂ : Substrate} {τ₁ τ₂ : Duration}
    (td₁ : TimerDef s₁ τ₁) (td₂ : TimerDef s₂ τ₂) : Task (s₁ ⊕Σ s₂) :=
  { inputAttribute  := from_product_attr (timer_attr_α td₁, timer_attr_α td₂),
    outputAttribute := from_product_attr (timer_attr_γ td₁, timer_attr_γ td₂) }

-- Combined Property (8) & (9):
-- ( (α,α) → (γ,γ) on [Tτ ⊕ Tτ']τ ) ✔ iff τ = τ'.
-- This means the task for simultaneous halting is possible if and only if durations are equal.
axiom timer_halting_iff_equal_duration
    {s₁ s₂ : Substrate} {τ₁ τ₂ : Duration} (td₁ : TimerDef s₁ τ₁) (td₂ : TimerDef s₂ τ₂)
    (h_dur_pos₁ : td₁.duration_is_positive) (h_dur_pos₂ : td₂.duration_is_positive) :
  Possible (task_both_halt_simultaneously td₁ td₂) ↔ (τ₁ = τ₂)

-- Synchrony of mutually isolated identical clocks (timers):
-- "any pair of isolated identical instances T ⊕ T ... cannot transform itself to any attribute
-- whose two constituent attributes are not identical – i.e. not of the form (X,X)."
-- This means if they start together (α,α), they cannot reach a state (X,Y) where X ≠ Y.
axiom timer_synchrony_property {s : Substrate} {τ : Duration} (td : TimerDef s τ)
    (attr_x attr_y : Attribute s) (h_attrs_differ : attr_x ≠ attr_y) :
  let task_desynchronize : Task (s ⊕Σ s) :=
    { inputAttribute  := from_product_attr (timer_attr_α td, timer_attr_α td),
      outputAttribute := from_product_attr (attr_x, attr_y) }
  Impossible task_desynchronize
  -- This should follow from `td.is_isolated_nc` and `isolated_composition_preserves_isolation`.

/-!
## Section 7: Dynamics
Recovering dynamics relative to timers.
-/

-- A physical variable V = {A(x)} indexed by a parameter x.
structure PhysicalVariable (Σ_pv : Substrate) where
  ParamType     : Type            -- Type of the index (e.g., ℝ)
  attributes    : ParamType → Attribute Σ_pv -- A(x)
  is_disjoint   : ∀ (x y : ParamType), x ≠ y →
                    Set.inter (attributes x) (attributes y) = (∅ : Set (State Σ_pv))
  is_non_static : ∀ (x : ParamType) (h_iso : IsIsolated Σ_pv),
                    ¬ IsStaticAttribute (attributes x) h_iso
  -- For expressing dV/dt, ParamType needs a way to be shifted by a Duration.
  add_duration_to_param : ParamType → Duration → ParamType -- x_new = x + Δt_param_equivalent

-- Dynamics: (A(x), TimerStart) → (A(x+Δt), TimerHalt) on Σ_pv ⊕Σ Timer_Δt is possible.
axiom dynamic_evolution_task_possible
    (Σ_pv : Substrate) (V : PhysicalVariable Σ_pv)
    (current_param_val : V.ParamType)
    (timer_s : Substrate) (Δt : Duration) (td_timer : TimerDef timer_s Δt) :
  let task_evolve_with_timer : Task (Σ_pv ⊕Σ timer_s) :=
    let attr_Ax       := V.attributes current_param_val
    let attr_Ax_plus_dt := V.attributes (V.add_duration_to_param current_param_val Δt)
    let attr_timer_α  := timer_attr_α td_timer
    let attr_timer_γ  := timer_attr_γ td_timer
    { inputAttribute  := from_product_attr (attr_Ax, attr_timer_α),
      outputAttribute := from_product_attr (attr_Ax_plus_dt, attr_timer_γ) }
  Possible task_evolve_with_timer

/-!
## Section 8: Relation to ‘timeless’ theories
Constructor theory provides an explanatory foundation.
The paper notes conditions like "possibility of good clocks" (timers), locality, etc.,
are expressed as requirements about possible/impossible tasks.
-/

/-!
## Section 9: Conclusions
This framework provides conditions for timer-supporting theories and recovering dynamics.
-/

#check Task -- Example check
