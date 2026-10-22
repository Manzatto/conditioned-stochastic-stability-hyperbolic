module
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLayerClassicalInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseFixedCutoffJacobian

/-! Only the actual computed inverse action's regular-space membership,
norm estimate and interpolation remain analytic inputs. The inverse map,
Jacobian weight, joint continuity and exact scalar cutoff duality are all
constructed from literal regular noise and the smooth reference measure. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff NNReal BoundedContinuousFunction
open LeanShared RegularNoise

structure TestActionInputs
    {E M ι Test TestCore : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
    [AddCommGroup TestCore] [Module ℂ TestCore]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (d : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (cutoff : M → ℝ) (view : Test →ₗ[ℂ] (M → ℂ))
    (inj : Function.Injective view) (qt : TestCore →ₗ[ℂ] Test) where
  window : ℝ≥0
  positive : 0 < window
  window_le : window ≤ J.window
  regular : ∀ ε, 0 < ε → ε ≤ window → InverseRegularTransfer.OrdinarySources view
    (J.fixedInverseMap ε) (J.fixedJacobianWeight d cutoff ε)
  smooth_continuous : ∀ c, Continuous (view (qt c))
  exponent : ℝ
  exponent_positive : 0 < exponent
  constant : ℝ≥0 → TestCore → FixedControl (ι := ι) → ℝ
  interpolation : ∀ ε (hp : 0 < ε) (hw : ε ≤ window) c z₀ z e, 0 ≤ e →
    (∀ x, ‖view ((regular ε hp hw).operator inj z (qt c)) x -
      view ((regular ε hp hw).operator inj z₀ (qt c)) x‖ ≤ e) →
    dist ((regular ε hp hw).operator inj z (qt c))
      ((regular ε hp hw).operator inj z₀ (qt c)) ≤ constant ε c z₀ * e ^ exponent

set_option maxHeartbeats 3200000 in
def TestActionInputs.analyticInputs
    {E M ι Parameters Test TestCore : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
    [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
    [AddCommGroup TestCore] [Module ℂ TestCore]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    {evaluate : Parameters → M → M} (p : Representation F Parameters evaluate)
    {V K G : Set M} (hK : IsCompact K) [CompactSpace K]
    (w : K → ℝ) (cutoff : M → ℝ) (cutoff_continuous : Continuous cutoff)
    (cutoff_support : Function.support cutoff ⊆ K) (cutoff_nonnegative : ∀ x, 0 ≤ cutoff x)
    (R : ℝ) (view : Test →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
    (qt : TestCore →ₗ[ℂ] Test) (J : InverseFamily F)
    (μ : Measure E) [IsAddHaarMeasure μ]
    (c : TestActionInputs J (FiniteSmoothReferenceCharts.canonicalData (E := E) (M := M)) cutoff view inj qt) :
    AnalyticInputs p (FiniteSmoothReferenceCharts.referenceMeasure (M := M) μ)
      V K G hK w (fun x => cutoff x.val) R view inj qt := by
  let d := FiniteSmoothReferenceCharts.canonicalData (E := E) (M := M)
  refine {
    inverseWindow := min c.window p.window
    inverseWindow_positive := lt_min c.positive p.window_positive
    inverseMap := J.fixedInverseMap
    inverseWeight := J.fixedJacobianWeight d cutoff
    inverseRegular := fun ε hp hw => c.regular ε hp (hw.trans (min_le_left _ _))
    inverse_joint := fun ε hp hw => J.fixedInverseMap_continuous ε hp
      ((hw.trans (min_le_left _ _)).trans c.window_le)
    inverse_weight_joint := ?_
    smooth_continuous := c.smooth_continuous
    inverseExponent := c.exponent
    inverseExponent_positive := c.exponent_positive
    inverseInterpolationConstant := c.constant
    inverse_interpolation := fun ε hp hw => c.interpolation ε hp (hw.trans (min_le_left _ _))
    jacobian := ?_ }
  · intro ε hp hw
    exact (J.fixedJacobianWeight_continuous d μ cutoff cutoff_continuous ε hp
      ((hw.trans (min_le_left _ _)).trans c.window_le)).comp
      (f := fun z : FixedControl (ι := ι) × M => (z.2,z.1)) continuous_swap
  · intro ε hp hw z f v
    have same : (fun y : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε y.2) y.1) =
        fun y => F.fixedMap ε y.1 y.2 := by
      funext y
      exact p.actual_fixedMap ε hp (hw.trans (min_le_right _ _)) y.1 y.2
    rw [same]
    exact J.fixed_cutoff_jacobian d μ K hK.measurableSet cutoff cutoff_support cutoff_nonnegative
      ε hp ((hw.trans (min_le_left _ _)).trans c.window_le) z f (view v)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
