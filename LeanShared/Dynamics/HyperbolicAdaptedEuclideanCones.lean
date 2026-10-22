module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCalculus
public import LeanShared.Analysis.HomeomorphDerivativeEquivalence
public import LeanShared.Analysis.OrthogonalDiagonalRatePerturbation

/-! Actual derivative and inverse-adjoint cone actions in the SAME
Euclidean adapted model, at the original one-step hyperbolic rate. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet OrthogonalProductCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem PatchSystem.euclideanDimension (system : PatchSystem b) :
    Module.finrank ℝ system.SplitModel = Module.finrank ℝ system.EuclideanModel := by
  simp [Module.finrank_prod]

@[expose] def PatchSystem.euclideanFirstProjection (system : PatchSystem b) :
    system.EuclideanModel →L[ℝ] system.EuclideanModel := firstProjection system.euclideanDimension

@[expose] def PatchSystem.euclideanSecondProjection (system : PatchSystem b) :
    system.EuclideanModel →L[ℝ] system.EuclideanModel := secondProjection system.euclideanDimension

theorem PatchSystem.actual_global_cones (system : PatchSystem b) {K : ℝ} (nonnegativeK : 0 ≤ K)
    (U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.unstableDimension))
    (S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.stableDimension))
    (stable : ‖S.toContinuousLinearMap‖ ≤ system.rate)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ system.rate)
    (inverseBound : ‖(system.euclideanDiagonal U S).symm.toContinuousLinearMap‖ ≤ K)
    (H : system.EuclideanModel ≃ₜ system.EuclideanModel)
    (smooth : Differentiable ℝ H) (inverseSmooth : Differentiable ℝ H.symm)
    (close : ∀ z, ‖fderiv ℝ H z - (system.euclideanDiagonal U S).toContinuousLinearMap‖ ≤
      OrthogonalDiagonalRatePerturbation.radius system.rate K) :
    (∀ z v, v ≠ 0 → v ∈ ProjectionConeTransversality.cone system.euclideanSecondProjection 1 →
      fderiv ℝ H z v ∈ interior (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (ProjectionConeRateMargin.opening system.rate))) ∧
    (∀ z v, v ≠ 0 → v ∈ ProjectionConeTransversality.cone system.euclideanFirstProjection 1 →
      (fderiv ℝ H.symm (H z)).adjoint v ∈
        interior (ProjectionConeTransversality.cone system.euclideanFirstProjection
          (ProjectionConeRateMargin.opening system.rate))) := by
  have diagonalEq : diagonal system.euclideanDimension U S = system.euclideanDiagonal U S := rfl
  have actions (z : system.EuclideanModel) :=
    OrthogonalDiagonalRatePerturbation.strict_actions system.euclideanDimension system.rate K
      system.rate_pos system.rate_lt_one nonnegativeK U S stable unstable
      (by simpa only [diagonalEq] using inverseBound)
      (HomeomorphDerivativeEquivalence.derivative H smooth inverseSmooth z)
      (by simpa only [HomeomorphDerivativeEquivalence.derivative_coe, diagonalEq] using close z)
  constructor
  · intro z v nonzero member
    have result := (actions z).1 v nonzero member
    change (HomeomorphDerivativeEquivalence.derivative H smooth inverseSmooth z).toContinuousLinearMap v ∈ _ at result
    rw [HomeomorphDerivativeEquivalence.derivative_coe] at result
    simpa only [PatchSystem.euclideanSecondProjection] using result
  · intro z v nonzero member
    simpa only [PatchSystem.euclideanFirstProjection, FakeLeafLinearImage.adjointEquiv_apply,
      HomeomorphDerivativeEquivalence.inverse_derivative_coe] using (actions z).2 v nonzero member

end LeanShared.HyperbolicAdaptedPatchSystem
