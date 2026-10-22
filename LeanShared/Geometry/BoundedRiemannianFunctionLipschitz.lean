module
public import LeanShared.Geometry.BoundedRiemannianMetric
public import LeanShared.Geometry.CompactRiemannianFunctionBounds
public import LeanShared.Geometry.RiemannianDerivativeDistanceBound
import Mathlib.Tactic.Linarith

/-! Genuine vector-valued C1 functions on a compact continuous-Riemannian
manifold are Lipschitz for its constructed bounded length metric. This
supplies the native-metric regularity of smooth test functions. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Manifold Bundle IsManifold
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

theorem function_exists_lipschitz
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (f : M → F) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f) :
    let _ : MetricSpace M := metric (E := E)
    ∃ L : ℝ≥0, LipschitzWith L f := by
  obtain ⟨C,hC,derivative⟩ := CompactRiemannianFunctionBounds.exists_norm_bound f smooth univ isCompact_univ
  obtain ⟨B,value⟩ := isCompact_univ.exists_bound_of_continuousOn smooth.continuous.continuousOn
  let C₀ : ℝ≥0 := ⟨C,hC.le⟩
  let B₀ : ℝ≥0 := ⟨max 0 B,le_max_left _ _⟩
  let _ : MetricSpace M := metric (E := E)
  change ∃ L : ℝ≥0, LipschitzWith L f
  refine ⟨max C₀ (2*B₀),?_⟩
  intro x y
  rw [metric_edist (E := E) x y]
  have actual := RiemannianDerivativeDistanceBound.riemannianEDist_le f smooth C hC
    (fun x => derivative x (mem_univ x)) x y
  rw [← IsRiemannianManifold.out] at actual
  rw [show C = (C₀ : ℝ) from rfl,ENNReal.ofReal_coe_nnreal] at actual
  by_cases small : riemannianEDist (𝓘(ℝ,E)) x y ≤ 1
  · rw [min_eq_left small,ENNReal.coe_max]
    exact actual.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le)
  · rw [min_eq_right (le_of_not_ge small),mul_one]
    have values (z : M) : ‖f z‖ ≤ (B₀ : ℝ) := (value z (mem_univ z)).trans (le_max_right _ _)
    have difference : ‖f x-f y‖ ≤ ((2*B₀ : ℝ≥0) : ℝ) := by
      calc
        _ ≤ ‖f x‖+‖f y‖ := norm_sub_le _ _
        _ ≤ (B₀ : ℝ)+(B₀ : ℝ) := add_le_add (values x) (values y)
        _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; ring
    have distance : edist (f x) (f y) ≤ (2*B₀ : ℝ≥0) := by
      rw [edist_dist,dist_eq_norm,← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal difference
    exact distance.trans (by exact_mod_cast le_max_right C₀ (2*B₀))

end LeanShared.BoundedRiemannianMetric
