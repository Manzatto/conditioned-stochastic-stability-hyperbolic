module

public import LeanShared.Geometry.CoherentCenteredCompactTargets
public import LeanShared.Geometry.FiniteSmoothReferenceChartImageUpper
public import LeanShared.MeasureTheory.UniformCoordinateHaarUpperBound

/-! Uniform upper smooth-reference volume comparison for the exact decoded
coordinate cylinders, with all density and frame constants constructed. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle Metric MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Bundle ENNReal

set_option maxHeartbeats 2400000 in
theorem exists_reference_volume_upper_bound
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace P] [BorelSpace P]
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {H : M → M} {K : Set M} {B δ : ℝ}
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B)
    (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B ∧
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (reference : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ] (x₀ : K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧
      ∀ x : K, ∀ s : Set P, IsOpen s → s ⊆ ball 0 ρ →
      (reference.measure μ) (decode d frame x '' s) ≤ C * (μ.map (linear d frame x₀).symm) s := by
  obtain ⟨targets, targetFacts, ρ, positiveρ, capture⟩ := exists_compact_targets d frame positiveB bounds
  have chartBounds (i : K) := reference.exists_chart_image_volume_upper_bound μ (chartAt E i.val)
    (chart_mem_maximalAtlas i.val) (targets i) (targetFacts i).1 (targetFacts i).2
  choose Ci finiteCi imageBound using chartBounds
  obtain ⟨M₀, positiveM₀, linearBounds⟩ := exists_uniform_linear_bound d frame positiveB bounds
  obtain ⟨C₀, positiveC₀, coordinateBound⟩ := UniformCoordinateHaarUpperBound.exists_bound μ
    (linear d frame x₀) M₀
  let D := 1 + ∑ i ∈ d.centers, Ci i
  have finiteD : D ≠ (∞ : ℝ≥0∞) := ENNReal.add_ne_top.mpr
    ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.mpr (fun i _ => finiteCi i)⟩
  have each (i : K) (hi : i ∈ d.centers) : Ci i ≤ D :=
    (Finset.single_le_sum (fun j _ => (show 0 ≤ Ci j from zero_le)) hi).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨ρ, positiveρ, D * ENNReal.ofReal C₀, ENNReal.mul_ne_top finiteD ENNReal.ofReal_ne_top,
    fun x s hs contained => ?_⟩
  let t := (fun y => chart d x x.val + y) '' ((linear d frame x) '' s)
  have openT : IsOpen t := (Homeomorph.addLeft (chart d x x.val)).isOpenMap _
    ((linear d frame x).toHomeomorph.isOpenMap _ hs)
  have captured : t ⊆ targets (index d x) := by
    rintro y ⟨v, ⟨z, hz, rfl⟩, rfl⟩
    have small : ‖z‖ < ρ := by simpa only [mem_ball, dist_zero_right] using contained hz
    exact capture x z small.le
  have image : (chartAt E (index d x).val).symm '' t = decode d frame x '' s := by
    simp only [t, Set.image_image]
    rfl
  have density := imageBound (index d x) t openT captured
  rw [image] at density
  have translate : μ t = μ ((linear d frame x) '' s) := by
    simp only [t, image_add_left, measure_preimage_add]
  calc
    _ ≤ Ci (index d x) * μ t := density
    _ ≤ D * μ t := mul_le_mul' (each _ (index_spec d x).1) le_rfl
    _ ≤ D * (ENNReal.ofReal C₀ * (μ.map (linear d frame x₀).symm) s) := by
      rw [translate]
      exact mul_le_mul' le_rfl
        (coordinateBound (linear d frame x) (linearBounds x).1 s hs.measurableSet)
    _ = _ := (mul_assoc _ _ _).symm

end LeanShared.CoherentCenteredCoordinateMaps
