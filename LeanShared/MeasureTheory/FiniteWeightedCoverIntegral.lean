module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! A finite weighted cover bounds an integral using weighted volumes,
without any disjointness assumption on the covering sets. -/
public noncomputable section
namespace LeanShared.FiniteWeightedCoverIntegral
open Set MeasureTheory
open scoped ENNReal BigOperators

theorem set_integral_le_sum {X I : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset I) (W : I → Set X) (S : Set X) (F : X → ℝ≥0∞)
    (cover : ∀ y ∈ S, ∃ i ∈ s, y ∈ W i) :
    ∫⁻ y in S, F y ∂μ ≤ ∑ i ∈ s, ∫⁻ y in W i, F y ∂μ := by
  classical
  have subset : S ⊆ ⋃ i : s, W i.val := by
    intro y hy
    obtain ⟨i, hi, inside⟩ := cover y hy
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,inside⟩
  calc
    _ ≤ ∫⁻ y in ⋃ i : s, W i.val, F y ∂μ := lintegral_mono_set subset
    _ ≤ ∑' i : s, ∫⁻ y in W i.val, F y ∂μ := lintegral_iUnion_le _ _
    _ = _ := Finset.tsum_subtype s (fun i => ∫⁻ y in W i, F y ∂μ)

theorem bound {X I : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset I) (W : I → Set X) (measurableW : ∀ i ∈ s, MeasurableSet (W i))
    (F : X → ℝ≥0∞) (a J : I → ℝ≥0∞) (C : ℝ≥0∞)
    (cover : ∀ y, F y ≠ 0 → ∃ i ∈ s, y ∈ W i)
    (pointwise : ∀ i ∈ s, ∀ y ∈ W i, F y ≤ a i * J i)
    (volume : ∀ i ∈ s, J i * μ (W i) ≤ C) :
    ∫⁻ y, F y ∂μ ≤ C * ∑ i ∈ s, a i := by
  classical
  have domination (y : X) : F y ≤ ∑ i ∈ s, (W i).indicator (fun _ => a i * J i) y := by
    by_cases zero : F y = 0
    · rw [zero]; exact bot_le
    obtain ⟨i, hi, inside⟩ := cover y zero
    calc
      F y ≤ a i * J i := pointwise i hi y inside
      _ = (W i).indicator (fun _ => a i * J i) y := (indicator_of_mem inside (fun _ => a i * J i)).symm
      _ ≤ ∑ k ∈ s, (W k).indicator (fun _ => a k * J k) y :=
        Finset.single_le_sum (f := fun k => (W k).indicator (fun _ => a k * J k) y) (fun k _ => bot_le) hi
  calc
    ∫⁻ y, F y ∂μ ≤ ∫⁻ y, ∑ i ∈ s, (W i).indicator (fun _ => a i * J i) y ∂μ :=
      lintegral_mono domination
    _ = ∑ i ∈ s, (a i * J i) * μ (W i) := by
      rw [lintegral_finsetSum s (fun i hi => measurable_const.indicator (measurableW i hi))]
      exact Finset.sum_congr rfl (fun i hi => lintegral_indicator_const (measurableW i hi) _)
    _ ≤ ∑ i ∈ s, a i * C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_assoc]
      exact mul_le_mul le_rfl (volume i hi) bot_le bot_le
    _ = C * ∑ i ∈ s, a i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _

end LeanShared.FiniteWeightedCoverIntegral
