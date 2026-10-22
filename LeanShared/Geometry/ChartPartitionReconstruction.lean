module
public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Geometry.SupportedChartExtension
/-! A genuine partition reconstructs every supported function, without a smoothness hypothesis. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ChartPartitionReconstruction
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  (e : J → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)

omit [FiniteDimensional ℝ E] in
theorem reconstruct (f : M → ℂ) (support : tsupport f ⊆ S) (x : M) :
    (∑ i : D.indices, SupportedChartExtension.function (e i)
      (ChartLocalization.coordinate (e i) (D.cutoff i) f) x) = f x := by
  classical
  have branch (i : D.indices) : SupportedChartExtension.function (e i)
      (ChartLocalization.coordinate (e i) (D.cutoff i) f) x = D.cutoff i x * f x := by
    by_cases hx : x ∈ (e i).source
    · rw [SupportedChartExtension.function, ite_eq_left hx]
      exact ChartLocalization.coordinate_chart (e i) (D.cutoff i) f x hx
    · rw [SupportedChartExtension.function, ite_eq_right hx]
      have zero : D.cutoff i x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (D.support i hs))
      rw [zero, zero_mul]
  simp_rw [branch]
  rw [← Finset.sum_mul]
  by_cases hx : x ∈ S
  · rw [D.partition x hx, one_mul]
  · have zero : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (support hs))
    rw [zero, mul_zero]
end LeanShared.ChartPartitionReconstruction
