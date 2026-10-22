module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! A strict finite principal cost budget admits one positive additive
margin for every fixed cylinder. This selection occurs after the block is
fixed, and introduces no new exponential count in the principal estimate. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.FiniteStrictCostBudget
variable {I : Type*} [Fintype I]

theorem exists_margin (q : I → ℝ) (A R : ℝ) (nonnegativeA : 0 ≤ A)
    (strict : A * ∑ i, q i < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ cost : I → ℝ, (∀ i, cost i ≤ q i + δ) →
      A * ∑ i, cost i < R := by
  let B := A * (Fintype.card I : ℝ)
  let δ := (R - A * ∑ i, q i) / (B + 1)
  have nonnegativeB : 0 ≤ B := mul_nonneg nonnegativeA (Nat.cast_nonneg _)
  have positiveDenominator : 0 < B + 1 := by linarith
  have positiveδ : 0 < δ := div_pos (sub_pos.mpr strict) positiveDenominator
  have identity : δ * (B+1) = R - A * ∑ i, q i :=
    div_mul_cancel₀ _ (ne_of_gt positiveDenominator)
  have sumIdentity : A * ∑ i, (q i + δ) = A * ∑ i, q i + B*δ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [B]
    ring
  have upper : A * ∑ i, (q i + δ) < R := by
    rw [sumIdentity]
    nlinarith
  refine ⟨δ,positiveδ,?_⟩
  intro cost bound
  exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => bound i)) nonnegativeA).trans_lt upper

end LeanShared.FiniteStrictCostBudget
