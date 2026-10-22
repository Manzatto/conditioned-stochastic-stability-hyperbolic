module

public import LeanShared.Dynamics.CompactInvariantProbability
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Invariant limit points of Cesaro averages of arbitrary varying
probabilities, as needed by the pressure variational principle. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal BoundedContinuousFunction
namespace LeanShared.CesaroProbability
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

@[expose] def measure (T : X → X) (μ : ProbabilityMeasure X) (n : ℕ) : Measure X :=
  ((n+1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range (n+1), (μ : Measure X).map (T^[j])

instance probability (T : X → X) (μ : ProbabilityMeasure X) (n : ℕ) :
    IsProbabilityMeasure (measure T μ n) := by
  constructor
  simp [measure, ENNReal.inv_mul_cancel]

@[expose] def probabilityMeasure (T : X → X) (μ : ProbabilityMeasure X) (n : ℕ) :
    ProbabilityMeasure X := ⟨measure T μ n, inferInstance⟩

theorem integral (T : X → X) (measurable : Measurable T) (μ : ProbabilityMeasure X) (n : ℕ)
    (f : X →ᵇ ℝ) :
    (∫ y, f y ∂measure T μ n) =
      (n+1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (n+1), ∫ y, f (T^[j] y) ∂(μ : Measure X) := by
  rw [measure,integral_smul_measure,integral_finsetSum_measure]
  · simp_rw [integral_map_of_stronglyMeasurable (measurable.iterate _) f.continuous.stronglyMeasurable]
    simp [ENNReal.toReal_add]
  · exact fun _ _ => f.integrable _

theorem integral_coboundary (T : X → X) (continuous : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) (f : X →ᵇ ℝ) :
    (∫ y, f (T y) ∂measure T μ n) - (∫ y, f y ∂measure T μ n) =
      (n+1 : ℝ)⁻¹ * ((∫ y, f (T^[n+1] y) ∂(μ : Measure X)) - ∫ y, f y ∂(μ : Measure X)) := by
  change (∫ y, (f.compContinuous ⟨T,continuous⟩) y ∂measure T μ n) - _ = _
  rw [integral T continuous.measurable,integral T continuous.measurable,←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  simpa only [BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
    Function.iterate_succ_apply',Function.iterate_zero_apply] using
    (Finset.sum_range_sub (fun j => ∫ y, f (T^[j] y) ∂(μ : Measure X)) (n+1))

/-- The starting probability may vary arbitrarily with the horizon. -/
theorem integral_coboundary_tendsto (T : X → X) (continuous : Continuous T)
    (μ : ℕ → ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    Tendsto (fun n => (∫ y, f (T y) ∂measure T (μ n) n) -
      (∫ y, f y ∂measure T (μ n) n)) atTop (𝓝 0) := by
  simp_rw [integral_coboundary T continuous]
  have bounded (n : ℕ) : ‖(n+1 : ℝ)⁻¹ *
      ((∫ y, f (T^[n+1] y) ∂(μ n : Measure X)) - ∫ y, f y ∂(μ n : Measure X))‖ ≤
      (n+1 : ℝ)⁻¹ * (2*‖f‖) := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
    have first := (f.compContinuous ⟨T^[n+1],continuous.iterate (n+1)⟩).norm_integral_le_norm (μ n : Measure X)
    have first' : ‖∫ y, f (T^[n+1] y) ∂(μ n : Measure X)‖ ≤ ‖f‖ :=
      first.trans (f.norm_compContinuous_le _)
    exact (norm_sub_le _ _).trans (by linarith [f.norm_integral_le_norm (μ n : Measure X)])
  apply squeeze_zero_norm bounded
  simpa only [one_div,zero_mul] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2*‖f‖)

/-- Every weak subsequential limit of the varying Cesaro probabilities
is invariant, without a prescribed invariant initial distribution. -/
theorem invariant_of_limit (T : X → X) (continuous : Continuous T)
    (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (φ : ℕ → ℕ) (mono : StrictMono φ)
    (convergence : Tendsto (fun n => probabilityMeasure T (μ (φ n)) (φ n)) atTop (𝓝 ν)) :
    MeasurePreserving T (ν : Measure X) (ν : Measure X) := by
  refine ⟨continuous.measurable,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable continuous.measurable f.continuous.stronglyMeasurable]
  have first := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp convergence)
    (f.compContinuous ⟨T,continuous⟩)
  have second := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp convergence) f
  have difference := (integral_coboundary_tendsto T continuous μ f).comp mono.tendsto_atTop
  exact sub_eq_zero.mp (tendsto_nhds_unique (first.sub second) difference)

end LeanShared.CesaroProbability
