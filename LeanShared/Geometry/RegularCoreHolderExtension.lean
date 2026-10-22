module

public import LeanShared.Analysis.HolderRealExtension
public import LeanShared.Analysis.RealHolderContinuity
public import LeanShared.Geometry.BoundedRiemannianHolderRegularity

/-! Scalar Hölder data on a core admit an actual global fractional-regular
extension. The extension is constructed using the bounded Riemannian
snowflake metric and the proved inverse-chart length comparison. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Bundle
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T3Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem exists_regular_core_extension (K : Set M) (f : M → ℝ) (α C : ℝ)
    (positive : 0 < α) (small : α < 1) (nonnegative : 0 ≤ C)
    (bound : ∀ x ∈ K, ∀ y ∈ K,
      |f x - f y| ≤ C * (@dist M (metric (E := E)).toDist x y) ^ α) :
    ∃ g : M → ℝ, FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α g ∧ EqOn f g K := by
  let _ : MetricSpace M := metric (E := E)
  obtain ⟨g, agreement, holder⟩ := HolderRealExtension.exists_extension α C positive small.le nonnegative K f bound
  have normBound (x y : M) : ‖g x - g y‖ ≤ C * dist x y ^ α := by
    simpa only [Real.norm_eq_abs] using holder x y
  have continuous : Continuous g := continuousOn_univ.mp
    (RealHolderContinuity.continuousOn univ g α C positive (fun x _ y _ => normBound x y))
  exact ⟨g, regular_of_native_holder positive small continuous nonnegative normBound, agreement⟩

end LeanShared.BoundedRiemannianMetric
