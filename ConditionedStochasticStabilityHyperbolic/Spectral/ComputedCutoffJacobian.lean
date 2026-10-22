module
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCutoffAdjoint
public import LeanShared.MeasureTheory.KilledJacobianBilinearDuality

/-! The analytic raw cutoff Jacobian identity is derived from the actual
scalar pushforward law. Cutoff support handles source killing exactly,
without a boundary-null or a completed-test duality assumption. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.ActualCutoffAdjoint
open Set MeasureTheory Measure
open scoped BoundedContinuousFunction ENNReal

set_option maxHeartbeats 1600000 in
theorem jacobian_from_pushforward
    {M Ω : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (σ : Measure M) (K : Set M) (measurableK : MeasurableSet K)
    (H : M ≃ₜ M) (F : M × Ω → M) (a : Ω) (same : ∀ x, F (x,a) = H x)
    (j : M → ℝ) (measurableJ : Measurable j) (nonnegativeJ : ∀ x, 0 ≤ j x)
    (law : σ.map H = σ.withDensity (fun x => ENNReal.ofReal (j x)))
    (w : M → ℝ) (support : Function.support w ⊆ K)
    (f : K →ᵇ ℂ) (g : M → ℂ) :
    (∫ x : K, raw K F (fun y => w y.val) a f x * g x.val ∂σ.comap Subtype.val) =
      ∫ y : K, f y * (((j y.val * w (H.symm y.val) : ℝ) : ℂ) * g (H.symm y.val))
        ∂σ.comap Subtype.val := by
  classical
  let f₀ := ComplexStrongFeller.zeroExtend K f
  have indicator : K.indicator f₀ = f₀ := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · simp [hx,f₀,ComplexStrongFeller.zeroExtend]
  have actual := LeanShared.JacobianBilinearDuality.supported_killed_integral
    σ H j measurableJ nonnegativeJ law K measurableK w support f₀ g
  rw [indicator] at actual
  calc
    _ = ∫ x in K, (w x : ℂ) * f₀ (H x) * g x ∂σ := by
      have convert := integral_subtype_comap (μ := σ) measurableK
        (fun x => (w x : ℂ) * f₀ (H x) * g x)
      simpa only [raw,same] using convert
    _ = ∫ y in K, f₀ y * (((j y * w (H.symm y) : ℝ) : ℂ) * g (H.symm y)) ∂σ := actual
    _ = _ := by
      have convert := integral_subtype_comap (μ := σ) measurableK
        (fun y => f₀ y * (((j y * w (H.symm y) : ℝ) : ℂ) * g (H.symm y)))
      simpa only [f₀,ComplexStrongFeller.zeroExtend_coe] using convert.symm

end ConditionedStochasticStabilityHyperbolic.ActualCutoffAdjoint
