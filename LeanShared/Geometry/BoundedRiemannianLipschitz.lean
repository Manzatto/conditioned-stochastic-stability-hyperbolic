module
public import LeanShared.Geometry.BoundedRiemannianMetric
public import LeanShared.Geometry.RiemannianDerivativeDistanceBound
public import LeanShared.Geometry.CompactRiemannianMFDeriv

/-! Actual C1 self maps of a compact continuous-Riemannian manifold are
Lipschitz for the constructed bounded length metric, without any assumption
identifying an arbitrary supplied compatible metric with length distance. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Manifold Bundle IsManifold
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

private theorem min_bound {a b C : ℝ≥0∞} (bound : a ≤ C * b) :
    min a 1 ≤ max C 1 * min b 1 := by
  by_cases small : b ≤ 1
  · rw [min_eq_left small]
    exact (min_le_left _ _).trans (bound.trans (mul_le_mul (le_max_left _ _) le_rfl zero_le zero_le))
  · rw [min_eq_right (le_of_not_ge small),mul_one]
    exact (min_le_right _ _).trans (le_max_right _ _)

theorem lipschitz_of_derivative_bound
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [T3Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (f : M → M) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f)
    (C : ℝ≥0) (positive : 0 < C)
    (bound : ∀ x, ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x‖ ≤ (C : ℝ)) :
    let _ : MetricSpace M := metric (E := E)
    LipschitzWith (max C 1) f := by
  let _ : MetricSpace M := metric (E := E)
  change LipschitzWith (max C 1) f
  intro x y
  rw [metric_edist,metric_edist,ENNReal.coe_max,ENNReal.coe_one]
  have actual := RiemannianDerivativeDistanceBound.riemannianEDist_le f smooth (C : ℝ)
    (by exact_mod_cast positive) bound x y
  rw [ENNReal.ofReal_coe_nnreal] at actual
  exact min_bound actual

theorem exists_lipschitz
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (f : M → M) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f) :
    let _ : MetricSpace M := metric (E := E)
    ∃ L : ℝ≥0, LipschitzWith L f := by
  obtain ⟨C,positive,bound⟩ := CompactRiemannianMFDeriv.exists_norm_bound f smooth univ isCompact_univ
  let C₀ : ℝ≥0 := ⟨C,positive.le⟩
  exact ⟨_,lipschitz_of_derivative_bound f smooth C₀ (by exact_mod_cast positive)
    (fun x => bound x (mem_univ _))⟩

end LeanShared.BoundedRiemannianMetric
