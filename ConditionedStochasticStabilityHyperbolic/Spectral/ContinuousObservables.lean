module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ConditionedAverages
public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Continuous-observable product measure and operator average

The conclusion uses the actual probability measure `g μ`. The rank-one gap
and representation of the eigenfunctional by integration are explicit inputs.
The path-law identification is proved in the separate canonical-chain module.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic

variable {X : Type*} [TopologicalSpace X]

/-- The transfer ratio with multiplication by a bounded continuous observable. -/
def continuousConditionedAverage (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (h : X →ᵇ ℝ) (x : X) (n : ℕ) : ℝ :=
  LeanShared.ConditionedOperators.conditionedAverage P
    (ContinuousLinearMap.mul ℝ (X →ᵇ ℝ) h)
    (BoundedContinuousFunction.evalCLM ℝ x) 1 n

/-- Expanded formula with powers totaling the survival horizon `n`. -/
theorem continuousConditionedAverage_eq (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (h : X →ᵇ ℝ) (x : X) (n : ℕ) :
    continuousConditionedAverage P h x n =
      ((n : ℝ)⁻¹ * ∑ i ∈ range n, ((P ^ i) (h * ((P ^ (n - i)) 1))) x) /
        ((P ^ n) 1) x := by
  simp [continuousConditionedAverage, LeanShared.ConditionedOperators.conditionedAverage,
    LeanShared.ConditionedOperators.operatorAverage, mul_apply_eq_comp, map_sum]

variable [MeasurableSpace X] [OpensMeasurableSpace X]
variable {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
  (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
  (μ : Measure X) [IsFiniteMeasure μ]
  (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)
  (hg0 : ∀ x, 0 ≤ d.eigenvector x)

include hmean hg0

/-- The candidate eigenvector/eigenmeasure product is a probability measure. -/
theorem eigenvector_product_isProbability :
    IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) := by
  apply LeanShared.eigenvectorMeasure_isProbability μ d.eigenvector
    (d.eigenvector.integrable μ) hg0
  rw [← hmean d.eigenvector]
  exact d.mean_eigenvector

omit [IsFiniteMeasure μ] in
/-- The continuous-observable operator part of `lem:spectral_gap_QEM`:
at every point positive on the eigenfunction, the exact ratio tends to its
integral against the normalized product probability. -/
theorem tendsto_continuousConditionedAverage (h : X →ᵇ ℝ) (x : X)
    (hx : 0 < d.eigenvector x) :
    Tendsto (continuousConditionedAverage P h x) atTop
      (𝓝 (∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector)) := by
  have hl := d.tendsto_conditionedAverage
    (ContinuousLinearMap.mul ℝ (X →ᵇ ℝ) h)
    (BoundedContinuousFunction.evalCLM ℝ x) hx
  have heq : d.mean ((ContinuousLinearMap.mul ℝ (X →ᵇ ℝ) h) d.eigenvector) =
      ∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector := by
    rw [hmean, LeanShared.integral_eigenvectorMeasure μ d.eigenvector
      d.eigenvector.continuous.measurable hg0]
    rfl
  rw [heq] at hl
  exact hl

/-- The limit statement together with the fact that its product measure is a probability. -/
theorem continuous_observable_probability_limit (h : X →ᵇ ℝ) (x : X)
    (hx : 0 < d.eigenvector x) :
    IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) ∧
      Tendsto (continuousConditionedAverage P h x) atTop
        (𝓝 (∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector)) := by
  exact ⟨eigenvector_product_isProbability d μ hmean hg0,
    tendsto_continuousConditionedAverage d μ hmean hg0 h x hx⟩

end ConditionedStochasticStabilityHyperbolic
