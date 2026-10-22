module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp

/-! Actual finite orbit averages are probability measures. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace LeanShared.EmpiricalProbability
variable {X : Type*} [MeasurableSpace X]

/-- The normalized counting measure of the first n+1 points of an orbit. -/
@[expose] def measure (T : X → X) (x : X) (n : ℕ) : Measure X :=
  ((n+1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range (n+1), Measure.dirac (T^[j] x)

instance probability (T : X → X) (x : X) (n : ℕ) :
    IsProbabilityMeasure (measure T x n) := by
  constructor
  simp [measure, ENNReal.inv_mul_cancel]

@[expose] def probabilityMeasure (T : X → X) (x : X) (n : ℕ) : ProbabilityMeasure X :=
  ⟨measure T x n, inferInstance⟩

theorem integral [MeasurableSingletonClass X] (T : X → X) (x : X) (n : ℕ)
    (f : X → ℝ) :
    (∫ y, f y ∂measure T x n) = (n+1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (n+1), f (T^[j] x) := by
  rw [measure, integral_smul_measure, integral_finsetSum_measure]
  · simp [ENNReal.toReal_add]
  · intro j _
    exact integrable_dirac (by simp)

theorem integral_coboundary [MeasurableSingletonClass X] (T : X → X) (x : X) (n : ℕ)
    (f : X → ℝ) :
    (∫ y, f (T y) ∂measure T x n) - (∫ y, f y ∂measure T x n) =
      (n+1 : ℝ)⁻¹ * (f (T^[n+1] x) - f x) := by
  rw [integral, integral, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    (Finset.sum_range_sub (fun j => f (T^[j] x)) (n+1))

end LeanShared.EmpiricalProbability
