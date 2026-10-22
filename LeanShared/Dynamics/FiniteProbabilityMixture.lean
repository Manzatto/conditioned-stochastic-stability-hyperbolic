module

public import LeanShared.Dynamics.FiniteEntropyConcavity
public import LeanShared.Dynamics.FiniteObservationEntropy
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Actual finite mixtures of probability measures and Shannon concavity
of every finite observation under those mixtures. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ENNReal
namespace LeanShared.FiniteProbabilityMixture
variable {X I : Type*} [MeasurableSpace X] [Fintype I]

@[expose] def measure (w : I → ℝ) (μ : I → ProbabilityMeasure X) : Measure X :=
  ∑ i, ENNReal.ofReal (w i) • (μ i : Measure X)

theorem probability (w : I → ℝ) (μ : I → ProbabilityMeasure X)
    (nonnegative : ∀ i, 0 ≤ w i) (total : ∑ i, w i=1) :
    IsProbabilityMeasure (measure w μ) := by
  constructor
  simp only [measure,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => nonnegative i),total,ENNReal.ofReal_one]

theorem real_apply (w : I → ℝ) (μ : I → ProbabilityMeasure X)
    (nonnegative : ∀ i, 0 ≤ w i) (A : Set X) :
    (measure w μ).real A=∑ i, w i*(μ i : Measure X).real A := by
  simp only [measure,Measure.real,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (nonnegative _)]

/-- This is concavity for the actual measure mixture, not a supplied
concavity inequality for preselected entropy scalars. -/
theorem observation_entropy_concave {J : Type*} [Fintype J]
    (w : I → ℝ) (μ : I → ProbabilityMeasure X)
    (nonnegative : ∀ i, 0 ≤ w i) (total : ∑ i, w i=1) (f : X → J) :
    ∑ i, w i*FiniteObservationEntropy.entropy (μ i : Measure X) f ≤
      FiniteObservationEntropy.entropy (measure w μ) f := by
  simpa only [FiniteObservationEntropy.entropy,real_apply w μ nonnegative] using
    FiniteEntropyConcavity.mixture w (fun i j => (μ i : Measure X).real (f ⁻¹' {j}))
      nonnegative total (fun _ _ => measureReal_nonneg)

end LeanShared.FiniteProbabilityMixture
