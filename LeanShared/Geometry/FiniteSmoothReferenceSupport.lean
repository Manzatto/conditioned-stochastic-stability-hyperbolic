module
public import LeanShared.Geometry.FiniteSmoothReferenceMeasure

/-! The constructed finite auxiliary volume charges every nonempty open set. -/
public noncomputable section
open Set Filter MeasureTheory Measure
open scoped Topology ENNReal
namespace LeanShared.FiniteSmoothReferenceCharts
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace E] [BorelSpace E]

instance Data.openPositive (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ] :
    IsOpenPosMeasure (d.measure μ) where
  open_pos W openW nonempty := by
    classical
    obtain ⟨p, hp⟩ := nonempty
    obtain ⟨x, hx, source, positive⟩ := d.cover p
    let e := chartAt E x
    let r := fun y => ENNReal.ofReal (d.density x y)
    let B := (e.target ∩ e.symm ⁻¹' W) ∩ {y | 0 < d.density x y}
    have openB : IsOpen B := (e.isOpen_inter_preimage_symm openW).inter
      (isOpen_lt continuous_const (d.smooth x).continuous)
    have memberB : e p ∈ B := by
      refine ⟨⟨e.map_source source, ?_⟩, positive⟩
      simpa only [mem_preimage, e.left_inv source] using hp
    have mass : 0 < μ B := openB.measure_pos μ ⟨e p, memberB⟩
    have measurableR : Measurable r := ENNReal.measurable_ofReal.comp (d.smooth x).continuous.measurable
    have positivePatch : 0 < CoordinatePatchMeasure.patch e μ r W := by
      rw [CoordinatePatchMeasure.patch, Measure.map_apply_of_aemeasurable
        (CoordinatePatchMeasure.inverse_aemeasurable e μ r) openW.measurableSet,
        withDensity_apply', setLIntegral_pos_iff measurableR]
      rw [Measure.restrict_apply' e.open_target.measurableSet]
      apply lt_of_lt_of_le mass
      apply measure_mono
      intro y hy
      exact ⟨⟨(ENNReal.ofReal_pos.mpr hy.2).ne', hy.1.2⟩, hy.1.1⟩
    exact (positivePatch.trans_le (d.patch_le μ hx W)).ne'
end LeanShared.FiniteSmoothReferenceCharts
