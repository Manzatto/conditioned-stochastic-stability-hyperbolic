module

public import LeanShared.Geometry.FiniteSmoothReferenceCompactVolumeLower

/-! Actual Haar volume of every open coordinate cylinder inside a compact
target patch is bounded by its smooth-reference manifold image volume. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff ENNReal

theorem Data.exists_chart_image_volume_bound
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set E) (compact : IsCompact K) (inside : K ⊆ c.target) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ t : Set E, IsOpen t → t ⊆ K →
      μ t ≤ C * (d.measure μ) (c.symm '' t) := by
  obtain ⟨C, finite, comparison⟩ := d.exists_compact_inverse_volume_bound μ c hc K compact inside
  refine ⟨C, finite, fun t ht subset => ?_⟩
  have openImage : IsOpen (c.symm '' t) := c.isOpen_image_symm_of_subset_target ht (subset.trans inside)
  have measurableInverse : AEMeasurable c.symm (μ.restrict K) :=
    (c.symm.continuousOn.mono inside).aemeasurable compact.measurableSet
  calc
    μ t = (μ.restrict K) t := by rw [Measure.restrict_apply ht.measurableSet, inter_eq_left.mpr subset]
    _ ≤ (μ.restrict K) (c.symm ⁻¹' (c.symm '' t)) :=
      measure_mono (fun x hx => mem_image_of_mem c.symm hx)
    _ = ((μ.restrict K).map c.symm) (c.symm '' t) :=
      (Measure.map_apply_of_aemeasurable measurableInverse openImage.measurableSet).symm
    _ ≤ _ := (Measure.le_iff.mp comparison) _ openImage.measurableSet

end LeanShared.FiniteSmoothReferenceCharts
