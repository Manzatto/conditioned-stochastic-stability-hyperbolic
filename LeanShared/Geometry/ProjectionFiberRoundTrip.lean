module
public import LeanShared.Geometry.ProjectionFiberTransport

/-! Coordinate conversion and native fiber transport are exact inverses. -/
public noncomputable section
namespace LeanShared.ProjectionFiberTransport
open Bundle
variable {B F:Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E:B→Type*) [∀b,NormedAddCommGroup (E b)] [∀b,NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

@[expose] def inverseCoordinates (e:Trivialization F (TotalSpace.proj (E:=E))) [e.IsLinear ℝ]
    (x y:B) (hx:x∈e.baseSet) (hy:y∈e.baseSet) (A:E x≃L[ℝ]E y) : F≃L[ℝ]F :=
  (e.continuousLinearEquivAt ℝ y hy).symm.trans
    (A.symm.trans (e.continuousLinearEquivAt ℝ x hx))

theorem inverseCoordinates_formula
    (e:Trivialization F (TotalSpace.proj (E:=E))) [e.IsLinear ℝ]
    (x y:B) (hx:x∈e.baseSet) (hy:y∈e.baseSet) (A:E x≃L[ℝ]E y) :
    (inverseCoordinates E e x y hx hy A).toContinuousLinearMap=
      (e.continuousLinearMapAt ℝ x).comp (A.symm.toContinuousLinearMap.comp (e.symmL ℝ y)) := by
  ext v
  change e.continuousLinearEquivAt ℝ x hx
    (A.symm ((e.continuousLinearEquivAt ℝ y hy).symm v))=_
  rw [Trivialization.coe_continuousLinearEquivAt_eq,
    Trivialization.symm_continuousLinearEquivAt_eq]
  rfl

theorem round_trip [VectorBundle ℝ F E]
    (e:Trivialization F (TotalSpace.proj (E:=E))) [e.IsLinear ℝ]
    (x y:B) (hx:x∈e.baseSet) (hy:y∈e.baseSet) (A:E x≃L[ℝ]E y) :
    map E e x y hx hy (inverseCoordinates E e x y hx hy A).symm=A := by
  ext v
  change (e.continuousLinearEquivAt ℝ y hy).symm
    ((e.continuousLinearEquivAt ℝ y hy)
      (A ((e.continuousLinearEquivAt ℝ x hx).symm
        (e.continuousLinearEquivAt ℝ x hx v))))=A v
  rw [ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply]
end LeanShared.ProjectionFiberTransport
