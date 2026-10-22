module
public import LeanShared.Dynamics.CesaroProbability
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-! A Gibbs estimate valid away from the two ends of a finite orbit word
passes to its actual Cesaro probability, with only `(k+1)/N` boundary loss. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.CesaroProbability

theorem sum_bound (a : ℕ → ℝ) (N k : ℕ) (K : ℝ) (nonnegativeK : 0 ≤ K)
    (probability : ∀ j < N, a j ≤ 1)
    (interior : ∀ j < N, 0 < j → j + k < N → a j ≤ K) :
    (∑ j ∈ Finset.range N, a j) ≤ (N : ℝ) * K + (k + 1 : ℕ) := by
  classical
  let bad := (Finset.range N).filter (fun j => j = 0 ∨ N ≤ j + k)
  have subset : bad ⊆ {0} ∪ Finset.Ico (N - k) N := by
    intro j hj
    obtain ⟨hjN, hj⟩ := Finset.mem_filter.mp hj
    rcases hj with zero | late
    · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr zero)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr
        ⟨by omega, Finset.mem_range.mp hjN⟩)
  have card : bad.card ≤ k + 1 := by
    have upper := (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
    simp only [Finset.card_singleton, Nat.card_Ico] at upper
    omega
  have term (j : ℕ) (hj : j ∈ Finset.range N) :
      a j ≤ K + if j = 0 ∨ N ≤ j + k then 1 else 0 := by
    by_cases boundary : j = 0 ∨ N ≤ j + k
    · rw [ite_eq_left boundary]
      linarith [probability j (Finset.mem_range.mp hj)]
    · rw [ite_eq_right boundary, add_zero]
      exact interior j (Finset.mem_range.mp hj) (by omega) (by omega)
  calc
    _ ≤ ∑ j ∈ Finset.range N, (K + if j = 0 ∨ N ≤ j + k then 1 else 0) :=
      Finset.sum_le_sum term
    _ = (N : ℝ) * K + (bad.card : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_const, mul_one, bad]
    _ ≤ _ := by
      have castCard : (bad.card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast card
      exact add_le_add le_rfl castCard

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem cylinder_mass_bound (T : X → X) (measurableT : Measurable T)
    (μ : ProbabilityMeasure X) (n k : ℕ) (K : ℝ) (nonnegativeK : 0 ≤ K)
    (U : Set X) (measurableU : MeasurableSet U)
    (interior : ∀ j < n + 1, 0 < j → j + k < n + 1 →
      (μ : Measure X).real ((T^[j]) ⁻¹' U) ≤ K) :
    (measure T μ n).real U ≤ K + ((k + 1 : ℕ) : ℝ) / (n + 1 : ℝ) := by
  have formula : (measure T μ n).real U = (n + 1 : ℝ)⁻¹ *
      ∑ j ∈ Finset.range (n + 1), (μ : Measure X).real ((T^[j]) ⁻¹' U) := by
    rw [measure, measureReal_ennreal_smul_apply]
    simp only [Measure.real, Measure.finsetSum_apply,
      ENNReal.toReal_inv, Nat.cast_add, Nat.cast_one]
    rw [ENNReal.toReal_sum (fun _ _ => by finiteness)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.map_apply (measurableT.iterate j) measurableU]
  rw [formula]
  have upper := sum_bound (fun j => (μ : Measure X).real ((T^[j]) ⁻¹' U))
    (n + 1) k K nonnegativeK (fun _ _ => measureReal_le_one) interior
  calc
    _ ≤ (n + 1 : ℝ)⁻¹ * ((n + 1 : ℕ) * K + (k + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left upper (by positivity)
    _ = _ := by
      push_cast
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_mul,
        div_eq_inv_mul]

end LeanShared.CesaroProbability
