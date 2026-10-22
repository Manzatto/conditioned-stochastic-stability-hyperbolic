module

public import LeanShared.Dynamics.HyperbolicUnstableJacobianContinuity

/-! Continuity of the literal thermodynamic potential is derived from the
actual tangent Jacobian and the actual positive weight on the core. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) : M → Type _)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.continuousOn_log_unstableJacobian (h : HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    ContinuousOn (fun x => Real.log (h.unstableJacobian x)) Λ :=
  h.continuousOn_unstableJacobian forward |>.log
    (fun x hx => ne_of_gt (h.unstableJacobian_positive (forward.mdifferentiable (by norm_num)) inverse x hx))

theorem HyperbolicData.continuousOn_potential (h : HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (g : M → ℝ) (continuous : ContinuousOn g Λ) (positive : ∀ x ∈ Λ, 0 < g x) :
    ContinuousOn (h.potential g) Λ :=
  (continuous.log (fun x hx => ne_of_gt (positive x hx))).sub
    (h.continuousOn_log_unstableJacobian forward inverse)

end LeanShared.HyperbolicBasicSet
