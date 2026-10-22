module
public import LeanShared.MeasureTheory.CoordinatePatchMeasure
public import Mathlib.Topology.Order.Compact

/-! Positive continuous coordinate densities give actual inverse-chart
volume domination on compact target patches. The constant is derived from
the attained positive minimum; no measure-domination field is assumed. -/
public noncomputable section
namespace LeanShared.CoordinatePatchMeasure
open Set MeasureTheory
open scoped ENNReal

theorem inverse_map_le_of_density_lower
    {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (e : OpenPartialHomeomorph M E) (μ : Measure E) (σ : Measure M)
    (r : E → ℝ) {K : Set E} (measurableK : MeasurableSet K) (contained : K ⊆ e.target)
    (reference : σ.restrict e.source = patch e μ (fun x => ENNReal.ofReal (r x)))
    (c : ℝ) (positive : 0 < c) (lower : ∀ x ∈ K, c ≤ r x) :
    (μ.restrict K).map e.symm ≤ (ENNReal.ofReal c)⁻¹ • σ := by
  let a := ENNReal.ofReal c
  let density := (μ.restrict e.target).withDensity (fun x => ENNReal.ofReal (r x))
  have nonzero : a ≠ 0 := (ENNReal.ofReal_pos.mpr positive).ne'
  have finite : a ≠ ∞ := ENNReal.ofReal_ne_top
  have first : a • μ.restrict K ≤
      (μ.restrict K).withDensity (fun x => ENNReal.ofReal (r x)) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableK] with x hx
    exact ENNReal.ofReal_le_ofReal (lower x hx)
  have second : (μ.restrict K).withDensity (fun x => ENNReal.ofReal (r x)) ≤ density := by
    apply Measure.le_iff.mpr
    intro B measurableB
    rw [withDensity_apply _ measurableB, withDensity_apply _ measurableB]
    exact lintegral_mono'
      (Measure.restrict_mono_measure (Measure.restrict_mono_set μ contained) B) le_rfl
  have comparison : μ.restrict K ≤ a⁻¹ • density := by
    calc
      μ.restrict K = a⁻¹ • (a • μ.restrict K) := by
        rw [smul_smul, ENNReal.inv_mul_cancel nonzero finite, one_smul]
      _ ≤ a⁻¹ • density := smul_le_smul_left _ (first.trans second)
  have measurableInverse : AEMeasurable e.symm density :=
    inverse_aemeasurable e μ (fun x => ENNReal.ofReal (r x))
  have mapped := Measure.map_mono_of_aemeasurable comparison (measurableInverse.smul_measure a⁻¹)
  rw [Measure.map_smul a⁻¹ measurableInverse] at mapped
  exact mapped.trans (smul_le_smul_left _ (by
    change patch e μ (fun x => ENNReal.ofReal (r x)) ≤ σ
    rw [← reference]
    exact Measure.restrict_le_self))

theorem exists_inverse_compact_volume_bound
    {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    (e : OpenPartialHomeomorph M E) (μ : Measure E) (σ : Measure M)
    (r : E → ℝ) {K : Set E} (compactK : IsCompact K) (contained : K ⊆ e.target)
    (continuousR : ContinuousOn r K) (positive : ∀ x ∈ K, 0 < r x)
    (reference : σ.restrict e.source = patch e μ (fun x => ENNReal.ofReal (r x))) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ (μ.restrict K).map e.symm ≤ C • σ := by
  rcases K.eq_empty_or_nonempty with empty | nonempty
  · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    simp only [empty, Measure.restrict_empty, Measure.map_zero, zero_smul, le_refl]
  · obtain ⟨x, hx, minimum⟩ := compactK.exists_isMinOn nonempty continuousR
    refine ⟨(ENNReal.ofReal (r x))⁻¹,
      ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (positive x hx)).ne', ?_⟩
    exact inverse_map_le_of_density_lower e μ σ r compactK.measurableSet contained reference
      (r x) (positive x hx) minimum

end LeanShared.CoordinatePatchMeasure
