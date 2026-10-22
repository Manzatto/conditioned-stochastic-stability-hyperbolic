module

public import LeanShared.Dynamics.EquilibriumWeightRestriction

/-! An equilibrium package for a reference weight gives exactly the potential
φ − log Ju when the actual weight exp φ agrees with it on the invariant core.
Only core agreement is used; no off-core regularity of φ is inferred. -/

public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M]
  {T : M ≃ₜ M} {Λ : Set M} {b : HyperbolicData (E := E) T Λ} {g : M → ℝ}

omit [BorelSpace M] in
theorem EquilibriumPackage.equilibrium_actual_phi (e : EquilibriumPackage b g)
    (φ : M → ℝ) (agreement : EqOn g (fun x => Real.exp (φ x)) Λ) :
    ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log (b.unstableJacobian x)) Λ e.state := by
  let changed := e.reweight (fun x => Real.exp (φ x)) (fun x hx => (agreement hx).symm)
  have same : b.potential (fun x => Real.exp (φ x)) =
      (fun x => φ x - Real.log (b.unstableJacobian x)) := by
    funext x
    exact congrArg (fun v => v - Real.log (b.unstableJacobian x)) (Real.log_exp (φ x))
  rw [← same]
  exact changed.equilibrium

omit [BorelSpace M] in
theorem EquilibriumPackage.unique_actual_phi (e : EquilibriumPackage b g)
    (φ : M → ℝ) (agreement : EqOn g (fun x => Real.exp (φ x)) Λ)
    (ν : ProbabilityMeasure M)
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log (b.unstableJacobian x)) Λ ν) : ν = e.state := by
  let changed := e.reweight (fun x => Real.exp (φ x)) (fun x hx => (agreement hx).symm)
  apply changed.unique ν
  have same : b.potential (fun x => Real.exp (φ x)) =
      (fun x => φ x - Real.log (b.unstableJacobian x)) := by
    funext x
    exact congrArg (fun v => v - Real.log (b.unstableJacobian x)) (Real.log_exp (φ x))
  exact same.symm ▸ equilibrium

end LeanShared.HyperbolicBasicSet
