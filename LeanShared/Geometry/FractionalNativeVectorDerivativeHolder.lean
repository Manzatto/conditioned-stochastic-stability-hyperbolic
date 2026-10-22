module

public import LeanShared.Geometry.FractionalRiemannianCoordinateDerivativeHolder
public import LeanShared.Geometry.NativeChartVectorDerivative
public import LeanShared.Geometry.DiffeomorphismDifferential

/-! Actual rectangular native differential matrices of vector-valued
C^(1+a) functions are Hölder on compact chart patches. The matrix is the
actual tangent differential, not an unrelated coordinate representative. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem Regular.compact_native_vector_derivative_holder {a : ℝ} (positive : 0 < a) (small : a < 1)
    {f : M → F} (regular : Regular (E := E) (F := F) (a + 1) f)
    (source : M) (K : Set M) (compact : IsCompact K) (inside : K ⊆ (chartAt E source).source) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ C ≥ 0, ∀ x ∈ K, ∀ y ∈ K,
      ‖NativeChartVectorDerivative.coordinateDifferential (E := E) f source x -
        NativeChartVectorDerivative.coordinateDifferential (E := E) f source y‖ ≤ C * dist x y ^ a := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  dsimp only
  obtain ⟨C, nonnegativeC, bound⟩ := regular.compact_coordinate_derivative_holder positive small
    source (0 : F) K compact inside (fun _ _ => by simp [chartAt_self_eq])
  have differentiable := regular.mdifferentiable (by linarith : 1 ≤ a + 1)
  refine ⟨C, nonnegativeC, fun x hx y hy => ?_⟩
  rw [← NativeChartVectorDerivative.fderiv_eq f differentiable source x (inside hx),
    ← NativeChartVectorDerivative.fderiv_eq f differentiable source y (inside hy)]
  simpa [chartAt_self_eq] using bound x hx y hy

end LeanShared.FractionalManifoldRegularity
