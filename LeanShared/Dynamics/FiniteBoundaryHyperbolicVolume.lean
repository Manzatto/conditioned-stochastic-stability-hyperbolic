module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicDifferential
public import LeanShared.MeasureTheory.PreimageVolumeLower

/-! Actual finite shooting converts an unstable principal-Jacobian upper
bound into a lower volume bound for the corresponding orbit cylinder. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
open MeasureTheory MeasureTheory.Measure Set
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace U] [CompleteSpace S]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ S]
  [MeasurableSpace (U × S)] [BorelSpace (U × S)] {N : ℕ}

theorem endpoint_volume_le (d : Data U S N) (μ : Measure (U × S)) [IsAddHaarMeasure μ]
    (B : Set (U × S)) (hB : MeasurableSet B)
    (differentiable : ∀ z ∈ d.shooting ⁻¹' B, ∀ i : Fin N,
      DifferentiableAt ℝ (d.nonlinear i) (d.evolve z i.val))
    (J : ℝ) (bound : ∀ z ∈ d.shooting ⁻¹' B,
      |(((ContinuousLinearMap.fst ℝ U S).comp
        (fderiv ℝ (fun w => d.evolve w N) z)).comp (ContinuousLinearMap.inl ℝ U S)).det| ≤ J) :
    μ B ≤ ENNReal.ofReal J * μ (d.shooting ⁻¹' B) := by
  apply PreimageVolumeLower.preimage_le μ d.shootingHomeomorph.symm B hB
    (fun z => ShootingJacobian.derivative (fderiv ℝ (fun w => d.evolve w N) z))
  · intro z hz
    exact (d.shooting_hasFDerivAt z (differentiable z hz)).hasFDerivWithinAt
  · intro z hz
    have equality := ShootingJacobian.determinant (fderiv ℝ (fun w => d.evolve w N) z)
    simpa only [ContinuousLinearMap.det] using
      (congrArg abs equality).le.trans (bound z hz)

end LeanShared.FiniteBoundaryHyperbolicTransform.Data
