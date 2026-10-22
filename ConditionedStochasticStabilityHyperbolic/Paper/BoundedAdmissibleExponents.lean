module

public import ConditionedStochasticStabilityHyperbolic.Paper.AdmissibleExponents

/-! The whole anisotropic tower can use one regular exponent below one,
regardless of r. This avoids higher-order regular test norms when producing
the concrete common test spaces. -/

@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.BoundedAdmissibleExponents
open RegularCoreApproximation

def loss (r : ℝ) : ℝ := min ((r - 1) / 16) (1 / 16)
def t (r : ℝ) (stage : Fin 3) : ℝ := (4 - (stage.val : ℝ)) * loss r
def s (r : ℝ) (stage : Fin 3) : ℝ := -(4 + (stage.val : ℝ)) * loss r
def regular (r : ℝ) : ℝ := 8 * loss r

theorem loss_positive {r : ℝ} (hr : 1 < r) : 0 < loss r := by
  dsimp [loss]
  exact lt_min (by linarith) (by norm_num)

theorem loss_order (r : ℝ) : 16 * loss r ≤ r - 1 := by
  have h : loss r ≤ (r - 1) / 16 := min_le_left _ _
  linarith

theorem regular_positive {r : ℝ} (hr : 1 < r) : 0 < regular r :=
  mul_pos (by norm_num) (loss_positive hr)

theorem regular_le_half (r : ℝ) : regular r ≤ 1 / 2 := by
  have h : loss r ≤ 1 / 16 := min_le_right _ _
  dsimp [regular]
  linarith

theorem margins {r : ℝ} (hr : 1 < r) (stage : Fin 3) :
    RegularityMargins r (t r stage) (s r stage) (regular r) := by
  have hη := loss_positive hr
  have hwidth := loss_order r
  have hk0 : 0 ≤ (stage.val : ℝ) := Nat.cast_nonneg _
  have hk2 : (stage.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ stage.isLt
  have hlower := mul_nonneg hk0 hη.le
  have hupper := mul_le_mul_of_nonneg_right hk2 hη.le
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [t, s, regular] <;> nlinarith

theorem negative_order_lt_regular {r : ℝ} (hr : 1 < r) (stage : Fin 3) :
    -(s r stage) < regular r := by
  have hη := loss_positive hr
  have hk2 : (stage.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ stage.isLt
  have hupper := mul_le_mul_of_nonneg_right hk2 hη.le
  dsimp [s, regular]
  nlinarith

theorem successive_t (r : ℝ) (i j : Fin 3) (h : j.val = i.val + 1) :
    t r j = t r i - loss r := by
  dsimp [t]
  rw [h, Nat.cast_add, Nat.cast_one]
  ring

theorem successive_s (r : ℝ) (i j : Fin 3) (h : j.val = i.val + 1) :
    s r j = s r i - loss r := by
  dsimp [s]
  rw [h, Nat.cast_add, Nat.cast_one]
  ring

end ConditionedStochasticStabilityHyperbolic.Paper.BoundedAdmissibleExponents
