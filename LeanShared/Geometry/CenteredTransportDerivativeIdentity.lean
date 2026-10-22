module
public import LeanShared.Geometry.ProjectionFiberTransport

/-! The inverse target-coordinate transport in a centered derivative is
exactly the corresponding native tangent-fiber transport. -/
public noncomputable section
namespace LeanShared.CenteredTransportDerivativeIdentity
open Bundle
variable {B F P Q:Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  (E:B→Type*) [∀b,NormedAddCommGroup (E b)] [∀b,NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

omit [VectorBundle ℝ F E] in
theorem physical_transport (e:Trivialization F (TotalSpace.proj (E:=E))) [e.IsLinear ℝ]
    (x y:B) (hx:x∈e.baseSet) (hy:y∈e.baseSet)
    (frame:Q≃L[ℝ]E y) (R:F≃L[ℝ]F) (D:P→L[ℝ]E x) :
    (frame.trans (e.continuousLinearEquivAt ℝ y hy)).symm.toContinuousLinearMap.comp
      (R.symm.toContinuousLinearMap.comp ((e.continuousLinearMapAt ℝ x).comp D)) =
      frame.symm.toContinuousLinearMap.comp
        ((ProjectionFiberTransport.map E e x y hx hy R.symm).toContinuousLinearMap.comp D) := by
  ext v
  change frame.symm ((e.continuousLinearEquivAt ℝ y hy).symm
    (R.symm (e.continuousLinearMapAt ℝ x (D v)))) =
    frame.symm (ProjectionFiberTransport.map E e x y hx hy R.symm (D v))
  rw [ProjectionFiberTransport.map_apply,Trivialization.symm_continuousLinearEquivAt_eq]
end LeanShared.CenteredTransportDerivativeIdentity
