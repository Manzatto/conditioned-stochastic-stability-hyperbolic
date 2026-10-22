module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! An eventual linear growth estimate has a global additive envelope.
The finite exceptional prefix is absorbed by a constructed finite sum. -/
public noncomputable section
open Filter
open scoped BigOperators
namespace LeanShared.EventuallyLinearEnvelope

theorem exists_bound (b : ℕ → ℝ) (P : ℝ)
    (eventual : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, b n ≤ (n : ℝ) * (P + ε)) :
    ∀ ε > 0, ∃ A : ℝ, ∀ n, b n ≤ (n : ℝ) * (P + ε) + A := by
  classical
  intro ε positive
  obtain ⟨N, bounded⟩ := eventually_atTop.mp (eventual ε positive)
  let A := ∑ j ∈ Finset.range N, max 0 (b j - (j : ℝ) * (P + ε))
  have nonnegative : 0 ≤ A := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨A, fun n => ?_⟩
  by_cases large : N ≤ n
  · exact (bounded n large).trans (le_add_of_nonneg_right nonnegative)
  · have term : max 0 (b n - (n : ℝ) * (P + ε)) ≤ A :=
      Finset.single_le_sum (f := fun j : ℕ => max 0 (b j - (j : ℝ) * (P + ε)))
        (fun _ _ => le_max_left _ _) (Finset.mem_range.mpr (lt_of_not_ge large))
    have lower : b n - (n : ℝ) * (P + ε) ≤ max 0 (b n - (n : ℝ) * (P + ε)) := le_max_right _ _
    linarith

end LeanShared.EventuallyLinearEnvelope
