module
public import LeanShared.Geometry.SmoothImmersionReferenceMetric
public import LeanShared.Analysis.ImmersionGramSmooth
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! Smoothness of the actual Euclidean immersion pullback metric, proved
from the genuine coordinate derivative and the smooth quadratic Gram map. -/
public noncomputable section
namespace LeanShared.SmoothImmersionReferenceMetric
open Bundle Manifold Set Filter ContinuousLinearMap
open scoped Topology Manifold ContDiff Bundle
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

@[expose] def coordinateGram (f : M → F) (center p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ImmersionPullbackInner.form (H := E)
    (inTangentCoordinates (𝓘(ℝ,E)) (𝓘(ℝ,F)) id f
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f) center p)

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
set_option maxHeartbeats 1600000 in
theorem coordinateGram_smooth (f : M → F)
    (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) ∞ f) (center : M) :
    ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞ (coordinateGram (E := E) f center) center := by
  have derivative := (smooth center).mfderiv_const (m := ∞) (by simp)
  exact ImmersionPullbackInner.contDiff_form.contMDiff.contMDiffAt.comp center derivative

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
@[expose] def smoothPullbackMetric (f : M → F)
    (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) ∞ f)
    (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)) :
    ContMDiffRiemannianMetric (𝓘(ℝ,E)) ∞ E (fun x : M => TangentSpace (𝓘(ℝ,E)) x) where
  inner := (pullbackMetric f injective).inner
  symm := (pullbackMetric f injective).symm
  pos := (pullbackMetric f injective).pos
  isVonNBounded := (pullbackMetric f injective).isVonNBounded
  contMDiff := by
    intro center
    rw [contMDiffAt_section]
    apply (coordinateGram_smooth (E := E) f smooth center).congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds E center] with p hp
    rw [hom_trivializationAt_apply]
    ext v w
    rw [inCoordinates_apply_eq₂
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hp)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hp) (by simp)]
    simp [coordinateGram,ContinuousLinearMap.inCoordinates,
      inTangentCoordinates,pullbackMetric,differential,ImmersionPullbackInner.form_apply]
    have base : p ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) center).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hp
    simp only [Trivialization.symmL_apply _ base]
    rfl

end LeanShared.SmoothImmersionReferenceMetric
