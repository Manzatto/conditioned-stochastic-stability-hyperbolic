module
public import LeanShared.Geometry.CompactRiemannianChartBounds
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Exact native tangent trivialization and normalized chart differential
identities. These identify actual bundle coordinates, including their
Riemannian fiber norms, with the centered-chart derivative. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.TangentChartTrivialization
variable {E M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
  [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]

omit [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)] in
theorem baseSet (center:M) :
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) center).baseSet =
      (chartAt E center).source := TangentBundle.trivializationAt_baseSet center

omit [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)] in
theorem forward {center x:M} (hx:x∈(chartAt E center).source) :
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) center).continuousLinearMapAt ℝ x =
      (NormedSpace.fromTangentSpace (𝕜:=ℝ) ((chartAt E center) x)).toContinuousLinearMap.comp
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (chartAt E center) x) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hx]
  ext v
  rfl
end LeanShared.TangentChartTrivialization
