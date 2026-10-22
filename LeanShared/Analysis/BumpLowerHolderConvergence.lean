module
public import LeanShared.Analysis.BumpLowerHolderApproximation
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual bump smoothing converges in each strictly lower Hölder graph
norm. Neither lower-norm convergence nor a smoothing source is assumed. -/
public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace LeanShared.BumpLowerHolderConvergence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {a b C : ℝ} (f : E →ᵇ ℂ)
  (hb : 0 ≤ b) (hab : b < a) (hC : 0 ≤ C)
  (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a)

/-- The actual higher-Hölder function has a canonical lower graph lift;
its existence is derived by splitting distances at one. -/
@[expose] def lift : BoundedHolderSpace.graph E b :=
  BoundedHolderSpace.ofBound E b f (max C (2 * ‖f‖)) (fun x y => by
    simpa only [Real.one_rpow, mul_one, div_one] using
      HolderInterpolation.increment_bound (a := a) (b := b) (C := C) (δ := 1)
        f hb hab hC zero_lt_one (fun x y => by simpa only [dist_eq_norm] using hf x y) x y)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Its function values are exactly the original function. -/
theorem physical_lift : BoundedHolderSpace.physical E b (lift f hb hab hC hf) = f :=
  BoundedHolderSpace.physical_ofBound _ _ _ _ _

/-- Quantitative error estimates imply convergence along ANY shrinking
family of genuine normalized bumps, with no regularity of the family assumed. -/
theorem error_tendsto_zero {I : Type*} {l : Filter I}
    (φ : I → ContDiffBump (0 : E))
    (radius : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => BumpLowerHolderApproximation.lowerError μ (φ i) f hb hab hC hf)
      l (𝓝 0) := by
  have ha : 0 < a := hb.trans_lt hab
  have hd : 0 < a - b := sub_pos.mpr hab
  have ta := (tendsto_const_nhds (x := C)).mul
    (((Real.continuous_rpow_const ha.le).tendsto 0).comp radius)
  have td := (tendsto_const_nhds (x := 2 * C)).mul
    (((Real.continuous_rpow_const hd.le).tendsto 0).comp radius)
  have limit : Tendsto (fun i => max (C * (φ i).rOut ^ a)
      (2 * C * (φ i).rOut ^ (a - b))) l (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne', Real.zero_rpow hd.ne', mul_zero, max_self, Function.comp_apply] using ta.max td
  exact squeeze_zero_norm (fun i =>
    BumpLowerHolderApproximation.lower_error_bound μ (φ i) f hb hab hC hf) limit

/-- The smooth functions themselves converge to the same literal rough
function in the lower Hölder graph, not merely uniformly or weakly. -/
theorem smoothing_tendsto {I : Type*} {l : Filter I}
    (φ : I → ContDiffBump (0 : E))
    (radius : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => lift (BumpSupportedRegularization.bounded μ (φ i) f) hb hab hC
      (BumpHolderRegularization.convolution_increment μ (φ i) f hf))
      l (𝓝 (lift f hb hab hC hf)) := by
  have error := error_tendsto_zero μ f hb hab hC hf φ radius
  have same (i : I) : BumpLowerHolderApproximation.lowerError μ (φ i) f hb hab hC hf +
      lift f hb hab hC hf =
      lift (BumpSupportedRegularization.bounded μ (φ i) f) hb hab hC
        (BumpHolderRegularization.convolution_increment μ (φ i) f hf) := by
    apply BoundedHolderSpace.physical_injective E b
    ext x
    change (BumpSupportedRegularization.function μ (φ i) f x - f x) + f x =
      BumpSupportedRegularization.function μ (φ i) f x
    exact sub_add_cancel _ _
  have result := error.add_const (lift f hb hab hC hf)
  simpa only [zero_add, same] using result
end LeanShared.BumpLowerHolderConvergence
