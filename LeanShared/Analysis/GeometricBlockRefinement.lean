module

public import LeanShared.Analysis.UniformGeometricTailBound
import Mathlib.Tactic.Ring

/-! Exponential estimates on windows whose radii are multiples of a
positive block length imply exponential estimates at every integer
radius.  The new rate is the positive block-th root of the old rate.
-/

public noncomputable section
namespace LeanShared.GeometricBlockRefinement
variable {P F : Type*} [NormedAddCommGroup F]

theorem exists_bound (f : P → F) (agreement : ℕ → P → P → Prop)
    (restrict : ∀ m n : ℕ, m ≤ n → ∀ p q, agreement n p q → agreement m p q)
    (block : ℕ) (positiveBlock : 0 < block) (θ C : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeC : 0 ≤ C)
    (bound : ∀ n : ℕ, ∀ p q, agreement (block * n) p q → ‖f q - f p‖ ≤ C * θ ^ n) :
    ∃ rate > 0, rate < 1 ∧ ∃ D ≥ 0,
      ∀ n : ℕ, ∀ p q, agreement n p q → ‖f q - f p‖ ≤ D * rate ^ n := by
  let rate := θ ^ (1 / (block : ℝ))
  have positiveExponent : 0 < 1 / (block : ℝ) := one_div_pos.mpr (by exact_mod_cast positiveBlock)
  have positiveRate : 0 < rate := Real.rpow_pos_of_pos positiveθ _
  have smallRate : rate < 1 := Real.rpow_lt_one positiveθ.le smallθ positiveExponent
  have ratePower : rate ^ block = θ := by
    dsimp only [rate]
    rw [← Real.rpow_natCast, ← Real.rpow_mul positiveθ.le]
    have exponent : (1 / (block : ℝ)) * (block : ℝ) = 1 := by
      exact div_mul_cancel₀ _ (by exact_mod_cast positiveBlock.ne')
    rw [exponent, Real.rpow_one]
  refine ⟨rate, positiveRate, smallRate, C / θ, div_nonneg nonnegativeC positiveθ.le, fun n p q same => ?_⟩
  have shorter : block * (n / block) ≤ n := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self n block
  have original := bound (n / block) p q (restrict _ _ shorter p q same)
  have longer : n ≤ block * (n / block + 1) := (Nat.lt_mul_div_succ n positiveBlock).le
  have power : θ ^ (n / block + 1) ≤ rate ^ n := by
    rw [← ratePower, ← pow_mul]
    exact pow_le_pow_of_le_one positiveRate.le smallRate.le longer
  have scale : (C / θ) * θ ^ (n / block + 1) = C * θ ^ (n / block) := by
    rw [pow_succ]
    field_simp
  calc
    _ ≤ C * θ ^ (n / block) := original
    _ = (C / θ) * θ ^ (n / block + 1) := scale.symm
    _ ≤ (C / θ) * rate ^ n :=
      mul_le_mul_of_nonneg_left power (div_nonneg nonnegativeC positiveθ.le)

end LeanShared.GeometricBlockRefinement
