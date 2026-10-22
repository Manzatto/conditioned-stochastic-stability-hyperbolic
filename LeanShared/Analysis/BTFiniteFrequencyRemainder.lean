module
public import LeanShared.Analysis.BTWeakDyadicRows

/-! The finite low-frequency square contributes only to the weak remainder.
Its constant may depend on the chosen cutoff level, while the principal
linked-row constant remains unchanged. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.BTFiniteFrequencyRemainder
open BTLinkedDyadicWeights

theorem sign_row_bound (t s loss : ℝ) (ht : 0 ≤ t) (hs : s ≤ 0)
    (hLoss : 0 ≤ loss) (N n : ℕ) (σ τ : Bool) (J : Finset ℕ) :
    (∑ l ∈ J, if max n l < N then
      (2 : ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l) else 0) ≤
      (N : ℝ)*(2 : ℝ)^((t-s+loss)*N) := by
  have out : exponent t s σ ≤ t := by cases σ <;> simp only [exponent] <;> linarith
  have inp : s ≤ exponent t s τ := by cases τ <;> simp only [exponent] <;> linarith
  have scalar (l : ℕ) (h : max n l < N) :
      exponent t s σ*n-(exponent t s τ-loss)*l ≤ (t-s+loss)*N := by
    have hn : (n : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt ((Nat.le_max_left n l).trans_lt h))
    have hl : (l : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt ((Nat.le_max_right n l).trans_lt h))
    have a := mul_le_mul_of_nonneg_right out (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have b := mul_le_mul_of_nonneg_right inp (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
    have c := mul_le_mul_of_nonneg_left hn ht
    have d := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ loss-s)
    nlinarith
  have point (l : ℕ) :
      (if max n l < N then (2 : ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l) else 0) ≤
        if l < N then (2 : ℝ)^((t-s+loss)*N) else 0 := by
    split_ifs with h hl hl
    · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (scalar l h)
    · exact False.elim (hl ((Nat.le_max_right n l).trans_lt h))
    · positivity
    · rfl
  have subset : J.filter (fun l => l < N) ⊆ Finset.range N := by
    intro l hl
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
  calc
    _ ≤ ∑ l ∈ J, if l < N then (2 : ℝ)^((t-s+loss)*N) else 0 :=
      Finset.sum_le_sum (fun l _ => point l)
    _ = ∑ l ∈ J.filter (fun l => l < N), (2 : ℝ)^((t-s+loss)*N) := by
      rw [Finset.sum_filter]
    _ ≤ ∑ l ∈ Finset.range N, (2 : ℝ)^((t-s+loss)*N) :=
      Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => by positivity)
    _ = _ := by simp

theorem row_bound (t s loss : ℝ) (ht : 0 ≤ t) (hs : s ≤ 0)
    (hLoss : 0 ≤ loss) (N n : ℕ) (σ : Bool) (J : Finset ℕ) :
    (∑ l ∈ J,∑ τ : Bool, if max n l < N then
      (2 : ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l) else 0) ≤
      2*((N : ℝ)*(2 : ℝ)^((t-s+loss)*N)) := by
  have a := sign_row_bound t s loss ht hs hLoss N n σ false J
  have b := sign_row_bound t s loss ht hs hLoss N n σ true J
  simpa only [Fintype.sum_bool,Finset.sum_add_distrib,two_mul] using add_le_add b a

end LeanShared.BTFiniteFrequencyRemainder
