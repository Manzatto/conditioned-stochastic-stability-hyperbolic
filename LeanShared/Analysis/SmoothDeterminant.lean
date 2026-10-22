module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The determinant of actual finite-dimensional continuous endomorphisms
is smooth, proved by its finite-basis Leibniz formula. -/
public section
namespace LeanShared.SmoothDeterminant
open scoped ContDiff

theorem contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ContDiff ℝ ∞ (fun L : E →L[ℝ] E => L.det) := by
  classical
  let b := Module.finBasis ℝ E
  have same : (fun L : E →L[ℝ] E => L.det) =
      fun L => (LinearMap.toMatrix b b L.toLinearMap).det := by
    funext L
    exact (LinearMap.det_toMatrix b L.toLinearMap).symm
  rw [same]
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  simp only [LinearMap.toMatrix_apply]
  change ContDiff ℝ ∞ (fun L : E →L[ℝ] E => b.repr (L (b i)) (σ i))
  exact ((b.coord (σ i)).toContinuousLinearMap.contDiff).comp
    (ContinuousLinearMap.apply ℝ E (b i)).contDiff

end LeanShared.SmoothDeterminant
