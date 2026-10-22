module
public import Mathlib.MeasureTheory.Function.Jacobian

/-! A genuine differential lower-Jacobian estimate yields domination of the
pushforward volume. No pushforward density or domination is assumed. This
is the local square-chart estimate used in finite submersion covers. -/
public section
open Set MeasureTheory
open scoped ENNReal
namespace LeanShared.DifferentialVolumeBound

theorem map_restrict_le_of_det_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} (measurable : Measurable f) {s : Set E} (hs : MeasurableSet s)
    (derivative : E → E →L[ℝ] E)
    (hasDerivative : ∀ x ∈ s, HasFDerivWithinAt f (derivative x) s x)
    (injective : Set.InjOn f s)
    (c : ℝ) (hc : 0 < c) (lower : ∀ x ∈ s, c ≤ |(derivative x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ := by
  let a := ENNReal.ofReal c
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hatop : a ≠ ∞ := ENNReal.ofReal_ne_top
  have densityLower : a • μ.restrict s ≤
      (μ.restrict s).withDensity (fun x => ENNReal.ofReal |(derivative x).det|) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (lower x hx)
  have mapped := Measure.map_mono densityLower measurable
  rw [Measure.map_smul a measurable.aemeasurable,
    map_withDensity_abs_det_fderiv_eq_addHaar μ hs.nullMeasurableSet hasDerivative injective] at mapped
  calc
    (μ.restrict s).map f = a⁻¹ • (a • (μ.restrict s).map f) := by
      rw [smul_smul, ENNReal.inv_mul_cancel ha0 hatop, one_smul]
    _ ≤ a⁻¹ • μ := by
      exact smul_le_smul_left _ (mapped.trans Measure.restrict_le_self)
end LeanShared.DifferentialVolumeBound
