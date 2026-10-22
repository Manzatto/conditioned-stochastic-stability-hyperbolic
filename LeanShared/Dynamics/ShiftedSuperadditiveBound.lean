module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A shifted superadditive sequence with asymptotic linear upper growth
has a uniform sharp upper bound at every horizon. This is the numerical
step converting specification products into Gibbs normalization bounds. -/
public section
namespace LeanShared.ShiftedSuperadditiveBound

private theorem nonpositive_of_bounded_nat_multiples (a C : ℝ)
    (bound : ∀ k : ℕ, (k + 1 : ℝ) * a ≤ C) : a ≤ 0 := by
  by_contra notNonpositive
  have positive : 0 < a := lt_of_not_ge notNonpositive
  obtain ⟨k, hk⟩ := exists_nat_gt (C / a)
  have strict : C < (k : ℝ) * a := (div_lt_iff₀ positive).mp hk
  have last := bound k
  linarith

theorem bound (b : ℕ → ℝ) (gap : ℕ) (P : ℝ)
    (superadditive : ∀ n, 0 < n → ∀ m, 0 < m → b n + b m ≤ b (n + m + gap))
    (growth : ∀ ε > 0, ∃ A : ℝ, ∀ n, b n ≤ (n : ℝ) * (P + ε) + A)
    (n : ℕ) (positive : 0 < n) : b n ≤ (n + gap : ℕ) * P := by
  have iterateBound (k : ℕ) : ((k : ℝ) + 1) * b n ≤ b ((k + 1) * n + k * gap) := by
    induction k with
    | zero => simp only [Nat.cast_zero, zero_add, one_mul, Nat.add_zero, Nat.zero_mul, le_refl]
    | succ k ih =>
      have next := superadditive ((k + 1) * n + k * gap) (by nlinarith) n positive
      have index : (k + 1) * n + k * gap + n + gap = (k + 1 + 1) * n + (k + 1) * gap := by ring
      rw [index] at next
      push_cast
      linarith
  apply le_of_forall_pos_le_add
  intro δ positiveδ
  let ε := δ / (n + gap : ℕ)
  have positiveε : 0 < ε := div_pos positiveδ (by exact_mod_cast (show 0 < n + gap by omega))
  obtain ⟨A, growthBound⟩ := growth ε positiveε
  have slope : b n - ((n + gap : ℕ) : ℝ) * (P + ε) ≤ 0 := by
    apply nonpositive_of_bounded_nat_multiples _ (A - (gap : ℝ) * (P + ε))
    intro k
    have upper := growthBound ((k + 1) * n + k * gap)
    have lower := iterateBound k
    push_cast at upper lower ⊢
    nlinarith
  have cancellation : ((n + gap : ℕ) : ℝ) * ε = δ :=
    mul_div_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt (show 0 < n + gap by omega)))
  nlinarith

end LeanShared.ShiftedSuperadditiveBound
