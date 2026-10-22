module

public import LeanShared.Geometry.FiniteSmoothReferenceLocalMeasure

/-! A smooth reference measure has a proved upper coordinate-volume bound
on each compact subset of a genuine smooth chart target. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff ENNReal

theorem Data.exists_chart_image_volume_upper_bound
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set E) (compact : IsCompact K) (inside : K ⊆ c.target) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ t : Set E, IsOpen t → t ⊆ K →
      (d.measure μ) (c.symm '' t) ≤ C * μ t := by
  obtain ⟨D, bounds⟩ := compact.exists_bound_of_continuousOn
    ((d.localDensity_continuousOn c hc).mono inside)
  refine ⟨ENNReal.ofReal (max 0 D), ENNReal.ofReal_ne_top, fun t openT subset => ?_⟩
  have imageSet : c ⁻¹' t ∩ c.source = c.symm '' t := by
    ext x
    constructor
    · rintro ⟨hx, source⟩
      exact ⟨c x, hx, c.left_inv source⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa only [Set.mem_preimage, c.right_inv (inside (subset hy))] using hy,
        c.map_target (inside (subset hy))⟩
  have measurableC : AEMeasurable c ((d.measure μ).restrict c.source) :=
    c.continuousOn.aemeasurable c.open_source.measurableSet
  have formula : (d.measure μ) (c.symm '' t) =
      ((μ.restrict c.target).withDensity (fun y => ENNReal.ofReal (d.localDensity c y))) t := by
    rw [← d.local_measure μ c hc, Measure.map_apply_of_aemeasurable measurableC openT.measurableSet,
      Measure.restrict_apply' c.open_source.measurableSet, imageSet]
  rw [formula, withDensity_apply _ openT.measurableSet]
  calc
    _ ≤ ∫⁻ _ in t, ENNReal.ofReal (max 0 D) ∂(μ.restrict c.target) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem openT.measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans ((bounds x (subset hx)).trans (le_max_right _ _)))
    _ = ENNReal.ofReal (max 0 D) * (μ.restrict c.target) t := by simp
    _ = _ := by rw [Measure.restrict_apply openT.measurableSet,
      inter_eq_left.mpr (subset.trans inside)]

end LeanShared.FiniteSmoothReferenceCharts
