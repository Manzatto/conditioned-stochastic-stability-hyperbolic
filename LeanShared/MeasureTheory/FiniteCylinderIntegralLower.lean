module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Positive coefficients over disjoint genuine cylinders sum to a lower
matrix-coefficient estimate. The Jacobian factors cancel multiplicatively,
without division or a hidden finiteness assumption. -/
public noncomputable section
namespace LeanShared.FiniteCylinderIntegralLower
open Set MeasureTheory
open scoped ENNReal
variable {X I : Type*} [MeasurableSpace X]

theorem bound (μ : Measure X) (s : Finset I) (W : I → Set X)
    (disjoint : (s : Set I).PairwiseDisjoint W) (measurable : ∀ i ∈ s, MeasurableSet (W i))
    (f : X → ℝ≥0∞) (v C : ℝ≥0∞) (a b : I → ℝ≥0∞)
    (volume : ∀ i ∈ s, v ≤ C * b i * μ (W i))
    (weight : ∀ i ∈ s, ∀ x ∈ W i, a i * b i ≤ f x) :
    v * (∑ i ∈ s, a i) ≤ C * ∫⁻ x, f x ∂μ := by
  have point (i : I) (hi : i ∈ s) : v * a i ≤ C * ∫⁻ x in W i, f x ∂μ := by
    have integral : (a i * b i) * μ (W i) ≤ ∫⁻ x in W i, f x ∂μ := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (measurable i hi) (weight i hi)
    calc
      v * a i ≤ (C * b i * μ (W i)) * a i := mul_le_mul' (volume i hi) le_rfl
      _ = C * ((a i * b i) * μ (W i)) := by ac_rfl
      _ ≤ _ := mul_le_mul' le_rfl integral
  calc
    _ = ∑ i ∈ s, v * a i := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s, C * ∫⁻ x in W i, f x ∂μ := Finset.sum_le_sum point
    _ = C * (∑ i ∈ s, ∫⁻ x in W i, f x ∂μ) := (Finset.mul_sum _ _ _).symm
    _ = C * ∫⁻ x in ⋃ i ∈ s, W i, f x ∂μ := by rw [lintegral_biUnion_finset disjoint measurable]
    _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

end LeanShared.FiniteCylinderIntegralLower
