module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A local three-point contraction forces exponential decay away from
both ends of a finite window. The proof peels the window one step at a
time, so no exponential estimate is a premise. -/
public section
namespace LeanShared.FiniteWindowContraction

theorem bound (d : ℕ → ℝ) (q M : ℝ) (nonnegative : 0 ≤ q) (n : ℕ)
    (bounded : ∀ j ≤ n, d j ≤ M)
    (contract : ∀ j, 0 < j → j < n →
      d j ≤ q * max (d (j - 1)) (max (d j) (d (j + 1)))) :
    ∀ j ≤ n, d j ≤ q ^ min j (n - j) * M := by
  have peel (k : ℕ) : ∀ j, k ≤ j → j + k ≤ n → d j ≤ q ^ k * M := by
    induction k with
    | zero =>
      intro j _ hj
      simpa only [pow_zero, one_mul] using bounded j (by omega)
    | succ k ih =>
      intro j hj hn
      have previous := ih (j - 1) (by omega) (by omega)
      have current := ih j (by omega) (by omega)
      have next := ih (j + 1) (by omega) (by omega)
      calc
        d j ≤ q * max (d (j - 1)) (max (d j) (d (j + 1))) :=
          contract j (by omega) (by omega)
        _ ≤ q * (q ^ k * M) := mul_le_mul_of_nonneg_left
          (max_le previous (max_le current next)) nonnegative
        _ = q ^ (k + 1) * M := by rw [pow_succ]; ring
  intro j hj
  exact peel (min j (n - j)) j (min_le_left _ _) (by omega)

end LeanShared.FiniteWindowContraction
