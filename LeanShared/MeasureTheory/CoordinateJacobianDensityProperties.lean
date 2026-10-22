module
public import LeanShared.MeasureTheory.CoordinateJacobianDensity
public import LeanShared.Geometry.ChartTransitionJacobian

/-! Measurability and positivity of actual transported chart densities. -/
public noncomputable section
namespace LeanShared.CoordinateJacobianDensity
open Set IsManifold
open scoped Topology Manifold ContDiff

theorem measurable
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M] [T2Space M]
    (e d : OpenPartialHomeomorph M E) (p : E → ℝ)
    (smooth : ContDiffOn ℝ 1 (e.symm.trans d).symm (e.symm.trans d).target)
    (continuous : Continuous p) (compact : HasCompactSupport p) (support : tsupport p ⊆ e.target) :
    Measurable (density e d p) := by
  classical
  have raw := (continuousOn e d p smooth continuous compact support).measurable_piecewise
    (f := density e d p) (g := fun _ => 0) continuousOn_const d.open_target.measurableSet
  have eq : d.target.piecewise (density e d p) (fun _ => 0) = density e d p := by
    funext y
    by_cases inside : y ∈ d.target
    · exact piecewise_eq_of_mem d.target _ _ inside
    · rw [piecewise_eq_of_notMem d.target _ _ inside]
      have outside : y ∉ (e.symm.trans d).target := fun h => inside h.1
      exact (ite_eq_right outside).symm
  rw [eq] at raw
  exact raw

theorem nonnegative
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    (e d : OpenPartialHomeomorph M E) (p : E → ℝ) (positive : ∀ x, 0 ≤ p x) (y : E) :
    0 ≤ density e d p y := by
  classical
  unfold density
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (positive _)
  · exact le_rfl

theorem positive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (e d : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (p : E → ℝ) (y : E) (inside : y ∈ (e.symm.trans d).target)
    (value : 0 < p ((e.symm.trans d).symm y)) : 0 < density e d p y := by
  classical
  change 0 < if y ∈ (e.symm.trans d).target then _ else _
  rw [ite_eq_left inside]
  exact mul_pos (abs_pos.mpr (ChartTransitionJacobian.inverse_det_ne_zero e d he hd y inside)) value

end LeanShared.CoordinateJacobianDensity
