module
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicDifferential
public import LeanShared.MeasureTheory.PreimageVolumeUpper

/-! The actual finite shooting map turns its principal-Jacobian lower
bound into an upper volume bound for the full inverse image of endpoint data. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
open MeasureTheory MeasureTheory.Measure Set
variable {U S:Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace U] [CompleteSpace S]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ S]
  [MeasurableSpace (U×S)] [BorelSpace (U×S)] {N:ℕ}

theorem reference_volume_le (d:Data U S N) (μ:Measure (U×S)) [IsAddHaarMeasure μ]
    (B:Set (U×S)) (measurable:MeasurableSet B)
    (smooth:∀z∈d.shooting ⁻¹' B,∀i:Fin N,
      DifferentiableAt ℝ (d.nonlinear i) (d.evolve z i.val))
    (J C:ℝ) (nonnegative:0≤C) (bound:∀z∈d.shooting ⁻¹' B,
      J≤C*|(((ContinuousLinearMap.fst ℝ U S).comp
        (fderiv ℝ (fun w=>d.evolve w N) z)).comp (ContinuousLinearMap.inl ℝ U S)).det|) :
    ENNReal.ofReal J*μ (d.shooting ⁻¹' B)≤ENNReal.ofReal C*μ B := by
  apply PreimageVolumeUpper.preimage_bound μ d.shootingHomeomorph.symm B measurable
    (fun z=>ShootingJacobian.derivative (fderiv ℝ (fun w=>d.evolve w N) z))
  · intro z hz
    exact (d.shooting_hasFDerivAt z (smooth z hz)).hasFDerivWithinAt
  · exact nonnegative
  · intro z hz
    have equality : |(ShootingJacobian.derivative (fderiv ℝ (fun w=>d.evolve w N) z)).det| =
        |(((ContinuousLinearMap.fst ℝ U S).comp (fderiv ℝ (fun w=>d.evolve w N) z)).comp
          (ContinuousLinearMap.inl ℝ U S)).det| := by
      simpa only [ContinuousLinearMap.det] using congrArg abs
        (ShootingJacobian.determinant (fderiv ℝ (fun w=>d.evolve w N) z))
    rw [equality]
    exact bound z hz
end LeanShared.FiniteBoundaryHyperbolicTransform.Data
