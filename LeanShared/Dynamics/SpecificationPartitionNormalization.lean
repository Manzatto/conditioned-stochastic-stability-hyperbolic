module

public import LeanShared.Dynamics.ShiftedSuperadditiveBound

/-! Specification product bounds and actual asymptotic log growth force a
uniform exponential upper bound on every positive partition horizon. No
normalization estimate is assumed. The zero-horizon product law is unused. -/
public noncomputable section
namespace LeanShared.SpecificationPartitionNormalization

theorem upper_bound (a : ℕ → ℝ) (positive : ∀ n, 0 < a n)
    (c : ℝ) (positiveC : 0 < c) (gap : ℕ) (P : ℝ)
    (product : ∀ n, 0 < n → ∀ m, 0 < m → c * a n * a m ≤ a (n + m + gap))
    (growth : ∀ ε > 0, ∃ A : ℝ, ∀ n, Real.log (a n) ≤ (n : ℝ) * (P + ε) + A) :
    ∀ n, 0 < n → a n ≤ Real.exp ((n + gap : ℕ) * P) / c := by
  let b := fun n => Real.log c + Real.log (a n)
  have additive (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) :
      b n + b m ≤ b (n + m + gap) := by
    have logarithm := Real.log_le_log (mul_pos (mul_pos positiveC (positive n)) (positive m))
      (product n hn m hm)
    rw [Real.log_mul (ne_of_gt (mul_pos positiveC (positive n))) (ne_of_gt (positive m)),
      Real.log_mul (ne_of_gt positiveC) (ne_of_gt (positive n))] at logarithm
    dsimp only [b]
    linarith
  have growthB : ∀ ε > 0, ∃ A : ℝ, ∀ n, b n ≤ (n : ℝ) * (P + ε) + A := by
    intro ε hε
    obtain ⟨A, bound⟩ := growth ε hε
    refine ⟨A + Real.log c, fun n => ?_⟩
    dsimp only [b]
    linarith [bound n]
  intro n hn
  have bound := ShiftedSuperadditiveBound.bound b gap P additive growthB n hn
  have logarithm : Real.log (a n) ≤ ((n + gap : ℕ) : ℝ) * P - Real.log c := by
    dsimp only [b] at bound
    linarith
  have exponential := Real.exp_le_exp.mpr logarithm
  rwa [Real.exp_log (positive n), Real.exp_sub, Real.exp_log positiveC] at exponential

end LeanShared.SpecificationPartitionNormalization
