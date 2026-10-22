module
public import LeanShared.Analysis.DifferentialVolumeBound
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! C1 local diffeomorphisms have locally bounded pushforward volume,
proved from the inverse function theorem and the exact Jacobian formula.
No density, volume bound, normal-form chart or uniform determinant estimate
is supplied as an input. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace LeanShared.DifferentialVolumeBound

theorem exists_local_volume_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} (measurable : Measurable f) {x : E}
    (smooth : ContDiffAt ℝ 1 f x) (e : E ≃L[ℝ] E)
    (derivative : HasStrictFDerivAt f (e : E →L[ℝ] E) x) :
    ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧
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
  refine ⟨u, openU, xu, (ENNReal.ofReal c)⁻¹, ?_, ?_⟩
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne'
  · exact map_restrict_le_of_det_lower μ measurable openU.measurableSet
      (fun z => fderiv ℝ f z)
      (fun z hz => (subset hz).2.1.hasFDerivAt.hasFDerivWithinAt)
      injective c hc (fun z hz => (subset hz).1.le)
end LeanShared.DifferentialVolumeBound
