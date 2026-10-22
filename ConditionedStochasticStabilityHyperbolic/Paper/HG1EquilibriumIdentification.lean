module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG1DominantOrdering
public import LeanShared.Dynamics.EquilibriumWeightRestriction
import all LeanShared.Dynamics.HyperbolicThermodynamics
import all LeanShared.Dynamics.EquilibriumWeightRestriction

/-! Literal HG1 deterministic source semantics. Real analytic pressure
scalars are identified with genuine EReal topological pressures before strict
ordering is derived. The equilibrium state is exactly the state named in HG1,
including replacement of the reference cutoff by the actual expφ weight. -/
public noncomputable section
open Set Bundle MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.HG1EquilibriumIdentification
open LeanShared HyperbolicBasicSet
variable {X E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace X] [ChartedSpace E X]
  [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace X] [BorelSpace X]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T)
  {g : X → ℝ} {A : Set X} (h : HG1 D g A)

omit [BorelSpace X] in
/-- The original state is the literal deterministic state already named by
HG1. Core agreement, not off-core cutoff equality, identifies its potential. -/
theorem equilibrium (φ : X → ℝ)
    (agree : EqOn g (fun x => Real.exp (φ x)) (D.core h.dominant)) :
    ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
      (D.core h.dominant) h.deterministic_equilibrium.state := by
  let changed := h.deterministic_equilibrium.reweight (fun x => Real.exp (φ x))
    (fun x hx => (agree hx).symm)
  have potential : (D.basic h.dominant).hyperbolic.potential (fun x => Real.exp (φ x)) =
      (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x)) := by
    funext x
    exact congrArg (fun v : ℝ => v - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
      (Real.log_exp (φ x))
  have sameState : changed.state = h.deterministic_equilibrium.state := rfl
  exact potential ▸ sameState ▸ changed.equilibrium

omit [BorelSpace X] in
theorem unique (φ : X → ℝ)
    (agree : EqOn g (fun x => Real.exp (φ x)) (D.core h.dominant))
    (ν : ProbabilityMeasure X)
    (state : ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
      (D.core h.dominant) ν) : ν = h.deterministic_equilibrium.state := by
  let changed := h.deterministic_equilibrium.reweight (fun x => Real.exp (φ x))
    (fun x hx => (agree hx).symm)
  apply changed.unique ν
  have potential : (D.basic h.dominant).hyperbolic.potential (fun x => Real.exp (φ x)) =
      (fun x => φ x - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x)) := by
    funext x
    exact congrArg (fun v : ℝ => v - Real.log ((D.basic h.dominant).hyperbolic.unstableJacobian x))
      (Real.log_exp (φ x))
  exact potential.symm ▸ state

variable {ℓ : ℕ} (retained : Global.ShiftedFiltrationGeometry.AdaptedSource T A D.core ℓ)
  (j : Fin ℓ) (selected : retained.index j = h.dominant)
  (p : Fin D.count → ℝ)
  (identity : ∀ i : Fin ℓ, D.pressure g (retained.index i) = (p (retained.index i) : EReal))

include selected identity in
omit [BorelSpace X] in
/-- The strict REAL pressure gap of the actual finite analytic array follows
from HG1 and ordinary finite-pressure identification. -/
theorem real_pressure_gap : ∀ i : Fin ℓ, i ≠ j →
    p (retained.index i) < p (retained.index j) := by
  intro i different
  have gap := ActualHG1DominantOrdering.pressure_gap T A ℓ D h retained j selected i different
  rw [identity i, identity j] at gap
  exact_mod_cast gap

include selected identity in
omit [BorelSpace X] in
/-- The selected real pressure is the pressure of the original HG1 state. -/
theorem selected_pressure : p (retained.index j) = h.deterministic_equilibrium.pressure := by
  have original := h.deterministic_equilibrium.pressure_identity
  change D.pressure g h.dominant = (h.deterministic_equilibrium.pressure : EReal) at original
  have selectedOriginal : D.pressure g (retained.index j) =
      (h.deterministic_equilibrium.pressure : EReal) := by
    rw [selected]
    exact original
  have same := (identity j).symm.trans selectedOriginal
  exact_mod_cast same

end ConditionedStochasticStabilityHyperbolic.Paper.HG1EquilibriumIdentification
