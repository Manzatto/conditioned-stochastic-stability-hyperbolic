module
public import LeanShared.Analysis.LocalDiffeomorphismVolumeBound

/-! A genuine differential lower-Jacobian estimate yields domination of the
pushforward volume. No pushforward density or domination is assumed. This
is the local square-chart estimate used in finite submersion covers. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff
namespace LeanShared.DifferentialVolumeBound

theorem map_restrict_le_of_local_det_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {s : Set E} (hs : MeasurableSet s)
    (derivative : E → E →L[ℝ] E)
    (hasDerivative : ∀ x ∈ s, HasFDerivWithinAt f (derivative x) s x)
    (injective : Set.InjOn f s)
    (c : ℝ) (hc : 0 < c) (lower : ∀ x ∈ s, c ≤ |(derivative x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ := by
  let a := ENNReal.ofReal c
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have densityLower : a • μ.restrict s ≤
      (μ.restrict s).withDensity (fun x => ENNReal.ofReal |(derivative x).det|) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (lower x hx)
  have baseMeas : AEMeasurable f (μ.restrict s) :=
    ContinuousOn.aemeasurable₀ (fun x hx => (hasDerivative x hx).continuousWithinAt)
      hs.nullMeasurableSet
  have densityMeas : AEMeasurable f
      ((μ.restrict s).withDensity (fun x => ENNReal.ofReal |(derivative x).det|)) :=
    baseMeas.mono_ac (withDensity_absolutelyContinuous _ _)
  have mapped : a • (μ.restrict s).map f ≤
      ((μ.restrict s).withDensity (fun x => ENNReal.ofReal |(derivative x).det|)).map f := by
    apply Measure.le_iff.mpr
    intro t ht
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply_of_aemeasurable baseMeas ht,
      Measure.map_apply_of_aemeasurable densityMeas ht]
    exact densityLower (f ⁻¹' t)
  rw [map_withDensity_abs_det_fderiv_eq_addHaar μ hs.nullMeasurableSet hasDerivative injective] at mapped
  calc
    (μ.restrict s).map f = a⁻¹ • (a • (μ.restrict s).map f) := by
      rw [smul_smul, ENNReal.inv_mul_cancel ha0 hatop, one_smul]
    _ ≤ a⁻¹ • μ := by
      exact smul_le_smul_left _ (mapped.trans Measure.restrict_le_self)
theorem exists_local_volume_bound_without_measurability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {x : E}
    (smooth : ContDiffAt ℝ 1 f x) (e : E ≃L[ℝ] E)
    (derivative : HasStrictFDerivAt f (e : E →L[ℝ] E) x) :
    ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ DifferentiableOn ℝ f u ∧ ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧
      (μ.restrict u).map f ≤ C • μ := by
  have nonzero : (fderiv ℝ f x).det ≠ 0 := by
    rw [derivative.hasFDerivAt.fderiv]
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  have positive : 0 < |(fderiv ℝ f x).det| := abs_pos.mpr nonzero
  let c := |(fderiv ℝ f x).det| / 2
  have hc : 0 < c := half_pos positive
  have lower : ∀ᶠ z in 𝓝 x, c < |(fderiv ℝ f z).det| :=
    ((ContinuousLinearMap.continuous_det.continuousAt.comp
      (smooth.continuousAt_fderiv one_ne_zero)).abs).eventually
        (Ioi_mem_nhds (half_lt_self positive))
  have differentiable : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
    (smooth.eventually (by decide)).mono (fun _ h => h.differentiableAt one_ne_zero)
  let inverse := derivative.toOpenPartialHomeomorph f
  have source : inverse.source ∈ 𝓝 x :=
    inverse.open_source.mem_nhds derivative.mem_toOpenPartialHomeomorph_source
  have neighbourhood : {z | c < |(fderiv ℝ f z).det| ∧
      DifferentiableAt ℝ f z ∧ z ∈ inverse.source} ∈ 𝓝 x :=
    lower.and (differentiable.and source)
  obtain ⟨u, subset, openU, xu⟩ := mem_nhds_iff.mp neighbourhood
  have injective : Set.InjOn f u := by
    have hi := inverse.injOn.mono (fun z hz => (subset hz).2.2)
    simpa only [inverse, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hi
  refine ⟨u, openU, xu, (fun z hz => (subset hz).2.1.differentiableWithinAt),
    (ENNReal.ofReal c)⁻¹, ?_, ?_⟩
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne'
  · exact map_restrict_le_of_local_det_lower μ openU.measurableSet
      (fun z => fderiv ℝ f z)
      (fun z hz => (subset hz).2.1.hasFDerivAt.hasFDerivWithinAt)
      injective c hc (fun z hz => (subset hz).1.le)
end LeanShared.DifferentialVolumeBound
