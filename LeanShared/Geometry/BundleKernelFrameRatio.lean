module

public import LeanShared.Geometry.BundleProjectionKernelEquiv
public import LeanShared.Geometry.NormDetFrameRatio

/-! A genuine ratio of native fiber Gram volumes is exactly its coordinate
kernel ratio in any valid bundle chart. The possibly nonisometric chart
volume cancels; it is never assumed to preserve the original metric. -/
public noncomputable section
namespace LeanShared.BundleEndomorphismCoordinates
open Bundle
variable {B F U V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [∀ b, FiniteDimensional ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem kernel_ratio_coordinates (e : Trivialization F (TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (P : ∀ b, E b →L[ℝ] E b) (b : B) (inside : b ∈ e.baseSet)
    (A : E b →L[ℝ] U) (C : E b →L[ℝ] V) :
    (A.comp (P b).ker.subtypeL).toLinearMap.normDet /
      (C.comp (P b).ker.subtypeL).toLinearMap.normDet =
    ((A.comp (e.symmL ℝ b)).comp (coordinates E e P b).ker.subtypeL).toLinearMap.normDet /
      ((C.comp (e.symmL ℝ b)).comp (coordinates E e P b).ker.subtypeL).toLinearMap.normDet := by
  let H := (kernelEquiv E e P b inside).symm
  have value (v : (coordinates E e P b).ker) : (H v).val = e.symmL ℝ b v.val := by
    have same := ContinuousLinearEquiv.ofSubmodules_symm_apply
      (e.continuousLinearEquivAt ℝ b inside) (map_kernel E e P b inside) v
    exact same.trans (congrFun (e.symm_continuousLinearEquivAt_eq inside) v.val)
  have sameA : (A.comp (P b).ker.subtypeL).comp H.toContinuousLinearMap =
      (A.comp (e.symmL ℝ b)).comp (coordinates E e P b).ker.subtypeL := by
    ext v
    exact congrArg A (value v)
  have sameC : (C.comp (P b).ker.subtypeL).comp H.toContinuousLinearMap =
      (C.comp (e.symmL ℝ b)).comp (coordinates E e P b).ker.subtypeL := by
    ext v
    exact congrArg C (value v)
  have result := NormDetFrameRatio.eq (A.comp (P b).ker.subtypeL) (C.comp (P b).ker.subtypeL) H
  rw [sameA, sameC] at result
  exact result.symm

end LeanShared.BundleEndomorphismCoordinates
